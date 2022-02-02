(function(exported){

// Statistics
function stats(data) {
    return {
        'min' : Math.min.apply(0, data),
        'max' : Math.max.apply(0, data),
        'mean' : mean(data),
        'median' : median(data),
        'std': std(data),
        'mode' : mode(data),
        'toString' : function() {
            return `{min: ${this.min.toFixed(2)},\tmax: ${this.max.toFixed(2)},\tmean: ${this.mean.toFixed(2)},\tmedian: ${this.median.toFixed(2)},\tstd: ${this.std.toFixed(2)},\tmode: ${this.mode.map(e => e.toFixed(2))}}`;
        }
    };
}

function min(arr) {
	return Math.min.apply(0, arr);
}

function mean(arr) {
        return arr.reduce((a,b) => a+b) / arr.length;
}

function median(arr) {
        arr.sort((a,b) => a-b);
        return (arr.length % 2) ? arr[(arr.length / 2) | 0] : mean([arr[arr.length/2 - 1], arr[arr.length / 2]]);
}

function mode(arr) {
        var counter = {};
        var mode = [];
        var max = 0;
        for (var i in arr) {
                if (!(arr[i] in counter)) {
                        counter[arr[i]] = 0;
                }
                counter[arr[i]]++;
                if (counter[arr[i]] == max) {
                        mode.push(arr[i]);
                } else if (counter[arr[i]] > max) {
                        max = counter[arr[i]];
                        mode = [arr[i]];
                }
        }
        return mode;
}

function variance(arr) {
    var x = mean(arr);
    return arr.reduce((pre, cur) => pre + ((cur - x)**2)) / (arr.length - 1);
}

function std(arr) {
    return Math.sqrt(variance(arr));
}

// Overload
Function.prototype.toSource = function() {
    return this.toString().slice(this.toString().indexOf('{')+1,-1);
}

/*
 Each chunk corresponds to the T[i]s in line 2 of algorithm 2
 in the paper (reduction via group testing):
 {T[1], ..., T[a + 1]} <- split(S, a + 1)
 */
Object.defineProperty(Array.prototype, 'chunk', {
    value: function(n){
		let results = [];
		let ceiled = this.length%n;
		let k = Math.ceil(this.length/n);
		let q = Math.floor(this.length/n);
		let c = 0;
		for (i=0; i<ceiled; i++) {
			results[i] = this.slice(c, c+k);
			c += k;
		}
		for (i; i<n; i++) {
			results[i] = this.slice(c, c+q);
			c += q;
		}
		return results;
    }
});

// Lists

// Send log to main thread
// Constants
const P = 4096;
const VERBOSE = false;
const NOLOG = false;

/*
 Threshold modified to that of Safari's eviction test, namely
 PLRU send under speculation.
 */
const THRESHOLD = 0.29;
const RESULTS = [];

// global vars to refactor
var first, next, n;

exported.build_evset = async function start(options) {
	// Parse settings
	const B = 8000;
	/*
	 I need to run Pepe Vila in targeted mode (as opposed to 
	 finding all eviction sets) so CONFLICT = false. I will
	 not need conflictSet.
	 */
	const CONFLICT = false;
	const ASSOC = 16;
	const STRIDE = 4096;

	// Prepare wasm instance
	const OFFSET = options.offset;
	const module = options.module;
	const memory = options.memory;

	log(`OFFSET: ${OFFSET}`);

	const instance = new WebAssembly.Instance(module, {env: {mem: memory}});
	// Memory view
	const view = new DataView(memory.buffer);

	if (!NOLOG) log('Prepare new evset');
	// memory, blocksize, start, victim, #ways, stride, offset
	const evset = new EvSet(view, B, P*2, P, ASSOC, STRIDE, OFFSET);
	first = true, next = CONFLICT;

	n = 0;
	const RETRY = 10;
	await new Promise(r => setTimeout(r, 10)); // timeout to allow counter
	do {
		let r = 0;
		while (!cb(instance, evset, CONFLICT) && ++r < RETRY && evset.victim) {
			if (VERBOSE) log('retry');
			first = false;
		}
		if (r < RETRY) {
			RESULTS.push(evset.refs); // save eviction set
			evset.refs = evset.del.slice();
			evset.del = [];
			evset.relink(); // from new refs
			next = CONFLICT;
			if (VERBOSE) log('Find next (', evset.refs.length, ')');
		}
		else
		{
			next = CONFLICT;
		}
	} while (CONFLICT && evset.vics.length > 0 && evset.refs.length > ASSOC);
	
	const SETS = [];
	for (const set of RESULTS) {
		for (let offset = 0; offset < STRIDE; offset += 64){
			SETS.push(set.map(num => {
				return {
					offset: num - (OFFSET*64) + offset,
				};
			}));
		}
	}

	log('Found ' + SETS.length + ' different eviction sets');

	return SETS;
}

function cb(instance, evset, findall) {

    let {wasm_hit, wasm_miss} = instance.exports;

    const REP = 6;
	const T = 1000;

	const CLOCK = 256; // hardcoded offset in wasm
	const VICTIM = evset.victim|0;
	const PTR = evset.ptr|0;

	function runCalibration(title, hit, miss, warm) {
		for (let i=0; i<T; i++) {
			hit(VICTIM);
			miss(VICTIM, 0);
		}
		if (!warm) {
			// real run
			let t_hit = hit(VICTIM);
			let t_miss = miss(VICTIM, PTR);
			// output
			if (VERBOSE) log ('--- ' + title + ' ---');
			if (VERBOSE) log ('Hit:\t' + (Array.isArray(t_hit) ? stats(t_hit) : t_hit));
			if (VERBOSE) log ('Miss:\t' + (Array.isArray(t_miss) ? stats(t_miss) : t_miss));
			if (VERBOSE) log ('-----------');
			// calc threshold
			if (Array.isArray(t_hit)) {
				t_hit = stats(t_hit).median;
			}
			if (Array.isArray(t_miss)) {
				t_miss = stats(t_miss).median;
			}
			if (t_hit > t_miss) {
				return 0;
			} else {
				return ((Number(t_miss) + Number(t_hit) * 2) / 3);
			}
		}
	}

	const wasmMeasureOpt = {
		hit : function hit(vic) {
			let t, total = [];
			for (let i=0; i<REP; i++) {
				t = wasm_hit(vic);
				total.push(Number(t));
			}
			return total;
		},
		miss : function miss(vic, ptr) {
			let t, total = [];
			for (let i=0; i<REP; i++) {
				t = wasm_miss(vic, ptr);
				total.push(Number(t));
			}
			return total;
		}
	}

	if (first) {
		runCalibration('Wasm measure opt', wasmMeasureOpt.hit, wasmMeasureOpt.miss, true);
		if (!THRESHOLD) {
			log('Error: calibrating');
			return false;
		}
		log('Calibrated threshold: ' + THRESHOLD);

		if (findall) {
			log('Creating conflict set...');
			evset.genConflictSet(wasmMeasureOpt.miss, THRESHOLD);
			log('Done: ' + evset.refs.length);
			first = false;
		}
	}

	if (next) {
		let t;
		do {
			evset.victim = evset.vics.pop();
			if (VERBOSE) log('\ttry victim', evset.victim);
			let e = 0;
			while (evset.victim && e < RESULTS.length) {
				if (median(wasmMeasureOpt.miss(evset.victim, RESULTS[e][0])) >= THRESHOLD) {
					RESULTS[e].push(evset.victim);
					if (VERBOSE) log('\tanother, this belongs to a previous eviction set');
					evset.victim = evset.vics.pop();
				}
				e += 1;
			}
			t = median(wasmMeasureOpt.miss(evset.victim, evset.ptr));
		} while (evset.victim && t < THRESHOLD);
		if (!evset.victim) {
			if (VERBOSE) log('No more victims');
			return false;
		}
		next = false;
	}

	if (VERBOSE) log ('Starting reduction...');
	evset.groupReduction(wasmMeasureOpt.miss, THRESHOLD);

	if (evset.refs.length === evset.assoc) {
		//if (!NOLOG) log('Victim addr: ' + evset.victim);
		//if (!NOLOG) log('Eviction set: ' + evset.refs);
		if (RESULTS.length % 13 === 0) {
			log(`Constructed ${RESULTS.length + 1} sets`);
		}
		evset.del = evset.del.flat();
		return true;
	} else {
		while (evset.del.length > 0) {
			evset.relinkChunk();
		}
		if (VERBOSE) log('Failed: ' + evset.refs.length);
		return false;
	}
}

function EvSet(view, nblocks, start=8192, victim=4096, assoc=16, stride=4096, offset=0) {

	const RAND = true;

	/* private methods */

	/*
	 From the paper (Sec V): we first allocate a big memory buffer (view) as a pool of
	 addresses from where we can suitably choose the candidate sets. genIndices
	 collects addressses from the buffer using a stride.
	 */
	this.genIndices = function (view, stride) {
		let arr = [], j = 0;
		for (let i=(stride)/4; i < (view.byteLength-this.start)/4; i += stride/4) {
			arr[j++] = this.start + this.offset + i*4;
			// offset is page offset of the victim (and all addresses in buffer)
			// the /4s and *4 cancel each other, but this seems to be for consistency
			// because Pepe Vila works over Uint32Arrays (view.setUint32)
		}
		arr.unshift(this.start + this.offset); // prepends to beginning of array
		return arr;
	}

	/*
	 From paper Sec V: for reducing the effect of hardware prefetching we use
	 a linked list to represent eviction sets, where each element is a pointer
	 to the next address. This ensures that all memory loads are executed in order.
	 We further randomize the order of elements.
	 */
	this.indicesToLinkedList =  function (buf, indices) {
		if (indices.length == 0) {
			this.ptr = 0;
			return;
		}
		let pre = this.ptr = indices[0];
		for (let i=1; i<indices.length; i++) {
			view.setUint32(pre, indices[i], true);
			pre = indices[i];
		}
		view.setUint32(pre, 0, true);
	}

	this.randomize = function (arr) {
		for (let i = arr.length; i; i--) {
			var j = Math.floor(Math.random() * i | 0) | 0;
			[arr[i - 1], arr[j]] = [arr[j], arr[i - 1]];
		}
		return arr;
	}

	this.init = function() {
		let indx = this.genIndices(view, stride);
		if (RAND) indx = this.randomize(indx);
		indx.splice(nblocks, indx.length); // select nblocks elements
		// From paper: randomly select N addresses in the buffer
		this.indicesToLinkedList(view, indx);
		return indx;
	}
	/* end-of-private */

	/* properties */
	this.start = start;
	this.offset = (offset&0x3f)<<6; // bits 6-12. Cache line offset truncated
	this.victim = victim+this.offset;
	view.setUint32(this.victim, 0, true); // lazy alloc
	this.assoc = assoc;
	this.ptr = 0;
	this.refs = this.init(); // refs is S in Algorithm 2 (the candidate set)
	this.del = []; // this is a stack of elements removed from the candidate set
	this.vics = []; // only used for finding all eviction sets
	/* end-of-properties */

	/* public methods */

	/*
	 From algorithm 2 in the paper: unlinkChunk is used to do S \ T[i], where 
	 one group out of the (assoc + 1) groups is removed from S (this.refs).
	 */
	this.unlinkChunk = function unlinkChunk(chunk) {
		let s = this.refs.indexOf(chunk[0]), f = this.refs.indexOf(chunk[chunk.length-1]);
		view.setUint32(this.refs[f], 0, true);
		this.refs.splice(s, chunk.length); // splice chunk indexes
		if (this.refs.length === 0) { // empty list
			this.ptr = 0;
		} else if (s === 0) { // removing first chunk
			this.ptr = this.refs[0];
		} else if (s > this.refs.length-1) { // removing last chunk
			view.setUint32(this.refs[this.refs.length-1], 0, true);
		} else { // removing middle chunk
			view.setUint32(this.refs[s-1], this.refs[s], true);
		}
		this.del.push(chunk); // right
	}

	/*
	 Reverses unlinkChunk, making S whole (the union of all T[i]).
	 */
	this.relinkChunk = function relinkChunk() {
		let chunk = this.del.pop(); // right
		if (chunk === undefined) {
			return;
		}
		this.ptr = chunk[0];
		if (this.refs.length > 0) {
			view.setUint32(chunk[chunk.length-1], this.refs[0], true);
		}
		if (typeof(chunk) === 'number') {
			this.refs.unshift(chunk); // left
		} else {
			this.refs.unshift(...chunk); // left
		}
	}

	/*
	 Algorithm 2 from the paper - threshold group testing.
	 */
	this.groupReduction = function groupReduction(miss, threshold) {
		// MAX is the amount of retries the algorithm will make for
		// one round of shrinking the eviction set size. This is to
		// account for false negatives leading to found not being
		// true even after one round of group testing, and false
		// positives eliminating ground truth elements.
		const MAX = 20;
		let i = 0, r = 0;
		// Minimum eviction set size is the # of ways in the LLC
		while (this.refs.length > this.assoc) {
			let m = this.refs.chunk(this.assoc+1);
			let found = false;
			// For each T[i] resulting from splitting S into (assoc + 1) groups
			for (let c in m) {
				// Exclude T[i] from S
				this.unlinkChunk(m[c]);
				// Replace this part with profile() in my current implementation
				let t = median(miss(this.victim, this.ptr));
				if (t < threshold) {
					this.relinkChunk();
				} else {
					found = true;
					break;
				}
			}
			if (!found) {
				r += 1;
				if (r < MAX) {
					// not found could be due to false positive in previous round
					// which caused a ground truth element to be eliminated. Retry.
					this.relinkChunk();
					// But if there are no previous rounds to revert to, exit with fail.
					if (this.del.length === 0) break;
				} else {
					// Out of retries, exit with fail.
					while (this.del.length > 0) {
						this.relinkChunk();
					}
					break;
				}
			}
			if (VERBOSE) if (!(i++ % 100)) print('\tremaining size: ', this.refs.length);
		}
	}

	/* 
	 Ignore everything below. This is code used for finding all eviction sets, not
	 for a specific victim address.
	 */

	this.linkElement = function linkElement(e) {
		if (e === undefined) return;
		this.ptr = e;
		if (this.refs.length > 0) {
			view.setUint32(e, this.refs[0], true);
		} else {
			view.setUint32(e, 0, true);
		}
		this.refs.unshift(e); // left
	}

	this.relink = function () {
		this.indicesToLinkedList(this.buffer, this.refs);
	}

	this.genConflictSet = function (miss, threshold) {
		let indices = this.refs; // copy original indices
		this.refs = [];
		this.vics = [];
		let pre = this.ptr = indices[0], i = 0, e, l = indices.length;
		for (i=0; i<Math.min(l, 800); i++) {
			e =  indices.pop();
			this.linkElement(e);
		}
		while (indices.length > 0) {
			e = indices.pop();
			view.setUint32(e, 0, true); // chrome's COW
			let t = miss(e, this.ptr);
			if (Array.isArray(t)) {
				t = median(t);
			}
			if (t < threshold) {
				this.linkElement(e);
			} else {
				this.vics.push(e);
				// break;
			}
		}
		first = true;
	}
	/* end-of-public */
}

})(self);