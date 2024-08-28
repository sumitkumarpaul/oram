use tfhe::boolean::backward_compatibility::client_key;
use tfhe::integer::bigint::U1024;
use tfhe::prelude::*;
use tfhe::{
    generate_keys, set_server_key, ConfigBuilder, FheBool, FheInt32, FheUint, FheUint1024,
    FheUint1024Id,
};
extern crate chrono;
use chrono::Local;
use core::num;
use once_cell::sync::Lazy;
use rand::distributions::{Distribution, Uniform};
use rand::rngs::ThreadRng;
use rand::Rng;
use rayon::prelude::*;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::fs;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::Write;
use std::io::{BufWriter, Result};
use std::io::{Read, Seek, SeekFrom};
use std::mem::MaybeUninit;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::sync::Mutex;
use std::thread;
use std::sync::atomic::{AtomicU64, Ordering};
use tfhe::prelude::*;
use tfhe::ClientKey;
static mut nxtRdBktLabel: u64 = 0; /* Lable of the bucket which will be read next */

/* Number of CPU cores */
macro_rules! NumCPUCores {
    () => {
        2048
    };
}

/* This must be initialized as macro, otherwise tree cannot be initialized statically */
macro_rules! N {
    () => {
        (2 as u64).pow(12) //2^12
    };
}

/* Since the aim is not to take lock on entire server tree, it must be initialized once and globally */
static g_tree: Lazy<Vec<Mutex<Bucket>>> = Lazy::new(|| {
    let mut local_tree: Vec<Mutex<Bucket>> = vec![];

    // Initialize the server buckets
    for i in 1..=(2 * N!() - 1) {
        // There will be 2N - 1 buckets in the tree
        unsafe {
            local_tree.push(Mutex::new(Bucket::new(i as u64)));
        }
    }

    local_tree
});

// Define a global mutable list (vector) wrapped in a Mutex for thread safety
static g_congested_buckets: Lazy<Mutex<Vec<u64>>> = Lazy::new(|| Mutex::new(vec![]));

macro_rules! printdbgln {
    ($dlvl:expr, $($arg:tt)*) => {
        if $dlvl > 0 {
            println!($($arg)*);
        }
    }
}

macro_rules! printdbg {
    ($dlvl:expr, $($arg:tt)*) => {
        if $dlvl > 0 {
            print!($($arg)*);
        }
    }
}

//64bit(8byte)*128=1KB block
macro_rules! NUMu64 {
    () => {
        2 //Temporarily it is changed to 2
    };
}

macro_rules! EMPTY {
    () => {
        2
    };
}

macro_rules! MOVE {
    () => {
        1
    };
}

macro_rules! NOT_MOVE {
    () => {
        0
    };
}
static mut N: u64 = (2 as u64).pow(12);
static mut L: u64 = 4;
static mut R: u64 = 1;
static mut C: u64 = 1; /* Initial number of replicas */
static mut Z: u64 = 8;
static mut ITR_CNT: u64 = 1024; /* The experiment will run for this amount of time */

static mut B: u64 = 4096; /* Common block size is: 4KB
                          But RLWE can encrypt 3KB per ciphertext.
                          So, block size must be set to multiple of 3KB.
                          Moreover, some place must be kept reserved for storing metadata */
static mut epoch: u64 = 14; //2(N-1)
static mut rate_ratio: u64 = 10; //Ratio of server's processing : Client's processing
static mut two: u64 = 2;
static mut tu: u64 = 0; /* Count of time unit */
static mut read_underflow_cnt: u64 = 0; /* The number of times the read operation failed */
static mut write_failure_cnt: u64 = 0; /* The number of times the write operation failed */
static mut write_failure_percentage: f64 = 0.0; /* The percentage of failed write operation */
static routing_congestion_cnt: AtomicU64 = AtomicU64::new(0);
static mut routing_congestion_percentage: f64 = 0.0; /* The percentage of congested steps during routing */
static mut num_congestion_blocks: u64 = 0; /* The number of blocks affected due to congestion */
static mut max_burst_cnt: u64 = 0; /* The number of blocks the client retrives in a burst */
static mut min_relax_cnt: u64 = 0; /* The amount of time (in terms of step processing), the client relaxes after each burst */
static mut since_access: u64 = 0; /* How many edges are processed since last signaling the CSI thread */
static mut since_print: u64 = 0; /* How many edges are processed since last status printed */
static mut status_print_freq: u64 = 0; /* After how many edge processing the status must be printed */
static mut global_max_bucket_load: u64 = 0; /* Maximum load occurred in any bucket */
static mut total_num_removed: u64 = 0; /* Total number of blocks removed from its leaf location */
static mut total_num_placed: u64 = 0; /* How many number of blocks are returned to place by the routing process */
static mut last_placement_tu: u64 = 0; /* When the last block is placed to its destined leaf */
static mut clrOld: bool = false; /* Clear previous prints */

#[derive(Debug)]
struct m {
    a: u64,
    x: u64,
}
#[derive(Debug)]
struct blk {
    m: m,
    //d: Vec<FheUint<FheUint1024Id>>,
    d: u64,
}

struct Bucket {
    b: u64,           //The label of this bucket
    blocks: Vec<blk>, //List holding the leaf identifiers of the blocks
    stat: Stat,
}

#[derive(Debug)]
struct Stat {
    access_cnt: u64,
    w_cnt: u64,
    r_cnt: u64,
    x_cnt: u64,
    out_up_cnt: u64,
    out_lft_cnt: u64,
    out_rgt_cnt: u64,
    in_up_cnt: u64,
    in_lft_cnt: u64,
    in_rgt_cnt: u64,
    sty_cnt: u64,
    max: u64,
    avg: f64,
    var: f64,    //Variance of occupancy
    sq_avg: f64, //Average of the square of the occupancy, required for calculating the variance
}

impl Clone for blk {
    fn clone(&self) -> blk {
        blk {
            m: m {
                a: self.m.a,
                x: self.m.x,
            },
            d: self.d,
        }
    }
}

impl blk {
    // Method to create a new Bucket
    fn new(id: u64, lf: u64) -> Self {
        blk {
            m: m { a: 0, x: 0 },
            //d: Vec::new(),
            d: 0 as u64,
        }
    }

    fn mk_empty(&mut self) {
        self.m.a = 0;
        self.m.x = 0;
    }

    fn copy_to(&self, dstblk: &mut blk) {
        dstblk.m.a = self.m.a;
        dstblk.m.x = self.m.x;
    }

    /* Fill all NUMu64! with same data */
    /*/
    fn fillData(&mut self, d: FheUint1024) {
        for _ in 0..NUMu64!() {
            self.d.push(d.clone());
        }
    }

    /* Print data */
    fn printData(&mut self, client_key: &ClientKey) {
        for _ in 0..NUMu64!() {
            //self.d.push(d.clone());
        }
    }
    */
}

impl Bucket {
    // Method to create a new Bucket
    unsafe fn new(label: u64) -> Self {
        Bucket {
            b: label,
            stat: Stat {
                access_cnt: 0,
                w_cnt: 0,
                r_cnt: 0,
                x_cnt: 0,
                out_up_cnt: 0,
                out_lft_cnt: 0,
                out_rgt_cnt: 0,
                in_up_cnt: 0,
                in_lft_cnt: 0,
                in_rgt_cnt: 0,
                sty_cnt: 0,
                max: 0,
                avg: 0.0,
                var: 0.0,    //Variance of occupancy
                sq_avg: 0.0, //Average of the square of the occupancy, required for calculating the variance
            },
            blocks: vec![blk::new(0, 0); Z as usize],
        }
    }

    // Method to add a u64(which contains the metadata m.x) in the place of 0
    unsafe fn insert(&mut self, x: u64, a: u64, d: u64) -> bool {
        let mut success: bool = false;

        if self.occupancy() < Z as usize {
            for slot in 0..Z as usize {
                if self.blocks[slot].m.x == 0 {
                    self.blocks[slot].m.x = x;
                    //self.blocks[slot].m.a = a;
                    //self.blocks[slot].d = d;
                    success = true;
                    break;
                }
            }
        }

        return success;
    }

    // Number of non empty slots
    fn occupancy(&self) -> usize {
        let mut occuCnt: usize = 0;

        unsafe {
            for i in 0..Z {
                if self.blocks[i as usize].m.x != 0 {
                    occuCnt += 1;
                }
            }
        }

        return occuCnt;
    }

    // Method to remove an item from non-empty slot of the bucket
    unsafe fn removeNxt(&mut self) -> u64 {
        let mut removed_item: u64 = 0;

        for slot in 0..Z as usize {
            if self.blocks[slot].m.x != 0 {
                removed_item = self.blocks[slot].d;
                self.blocks[slot].m.x = 0; //Mark the slot as empty
                break;
            }
        }

        return removed_item;
    }

    // Method to remove an item from the stated index and insert 0 in that place
    fn remove(&mut self, index: usize) -> u64 {
        let mut removed_item: u64 = self.blocks[index].d;
        self.blocks[index].m.x = 0;

        return removed_item;
    }

    // Method to remove an item by its value
    /*
    fn removeVal(&mut self, value: u64) -> u64 {
        let mut removed_item: u64 = 0;

        if let Some(pos) = self.blocks.iter().position(|&x| x == value) {
            removed_item = self.blocks[pos];
            self.blocks.remove(pos);
        }

        return removed_item;
    }
    */

    // Method to update the statistics of the bucket
    fn calc_stat(&mut self) -> Stat {
        /* Store previous statistics */
        let mut prev_avg: f64 = self.stat.avg;

        let mut prev_avg_sq: f64 = self.stat.sq_avg;

        let mut total: u64 = (prev_avg * (self.stat.access_cnt as f64)) as u64;

        let mut sq_total: u64 = (prev_avg_sq * (self.stat.access_cnt as f64)) as u64;

        self.stat.access_cnt += 1;

        let mut current: u64 = self.occupancy() as u64;
        total += current as u64;
        sq_total += current.pow(2) as u64;

        self.stat.avg = (total as f64 / self.stat.access_cnt as f64) as f64;

        self.stat.sq_avg = (sq_total as f64 / self.stat.access_cnt as f64) as f64;

        /* var(X) = E[x^2] - E[x]^2*/
        self.stat.var = self.stat.sq_avg - (self.stat.avg * self.stat.avg);

        if current > self.stat.max {
            self.stat.max = current;

            unsafe {
                if current > global_max_bucket_load {
                    global_max_bucket_load = current;
                }
            }
        }

        Stat {
            access_cnt: self.stat.access_cnt,
            w_cnt: self.stat.w_cnt,
            r_cnt: self.stat.r_cnt,
            x_cnt: self.stat.x_cnt,
            out_up_cnt: self.stat.out_up_cnt,
            out_lft_cnt: self.stat.out_lft_cnt,
            out_rgt_cnt: self.stat.out_rgt_cnt,
            in_up_cnt: self.stat.in_up_cnt,
            in_lft_cnt: self.stat.in_lft_cnt,
            in_rgt_cnt: self.stat.in_rgt_cnt,
            sty_cnt: self.stat.sty_cnt,
            max: self.stat.max,
            avg: self.stat.avg,
            var: self.stat.var,       //Variance of occupancy
            sq_avg: self.stat.sq_avg, //Average of the square of the occupancy, required for calculating the variance
        }
    }

    // Method printing the statistics of the bucket
    // The printing order is always: access_count, average, variance, maximum, current content
    fn print_detailed_stat(&mut self, file: &mut File) -> Stat {
        // Handle the Result returned by writeln! using match
        if let Err(e) = writeln!(
            file,
            "Bucket[{}],\
    {},\
    {},\
    {},\
    {},\
    {},\
    {:.2},\
    {:.2},\
    {},\
    {},\
    {},\
    {},\
    {},\
    {},\
    {},\
    {}",
            self.b,
            self.stat.access_cnt,
            self.stat.r_cnt,
            self.stat.w_cnt,
            self.stat.x_cnt,
            self.occupancy(),
            self.stat.avg,
            self.stat.var,
            self.stat.max,
            self.stat.out_up_cnt,
            self.stat.out_lft_cnt,
            self.stat.out_rgt_cnt,
            self.stat.in_up_cnt,
            self.stat.in_lft_cnt,
            self.stat.in_rgt_cnt,
            self.stat.sty_cnt
        ) {
            eprintln!("Failed to write to file: {}", e);
        }
        Stat {
            access_cnt: self.stat.access_cnt,
            w_cnt: self.stat.w_cnt,
            r_cnt: self.stat.r_cnt,
            x_cnt: self.stat.x_cnt,
            out_up_cnt: self.stat.out_up_cnt,
            out_lft_cnt: self.stat.out_lft_cnt,
            out_rgt_cnt: self.stat.out_rgt_cnt,
            in_up_cnt: self.stat.in_up_cnt,
            in_lft_cnt: self.stat.in_lft_cnt,
            in_rgt_cnt: self.stat.in_rgt_cnt,
            sty_cnt: self.stat.sty_cnt,
            max: self.stat.max,
            avg: self.stat.avg,
            var: self.stat.var,       //Variance of occupancy
            sq_avg: self.stat.sq_avg, //Average of the square of the occupancy, required for calculating the variance
        }
    }
}

fn main() {
    let mut M = m { a: 5, x: 5 };

    //let mut block = blk { m: M, d: [5, 5] };

    let mut Tcur: u64;
    let mut x: u64;
    let mut w: u64;

    unsafe {
        Tcur = 0;
        let mut rng = rand::thread_rng();
        x = rng.gen_range(two.pow(L as u32 - 1)..(two.pow(L as u32) - 1));
        w = rng.gen_range(1..(two.pow((L - R) as u32) - 1));

        x = rng.gen_range(two.pow(L as u32 - 1)..(two.pow(L as u32) - 1));
        w = rng.gen_range(1..(two.pow((L - R) as u32) - 1));

        //block.m = M;
        //block.d = [5,5];

        //Comment out some experiments
        if false {
            /* Experiment 1 */
            oram_exp(
                two.pow(26), /* Kept block size 4KB as per other ORAM paper
                                256GB remote storage.
                                2^26*4KB blocks. With compute canada resource cannot simulate larger remote storage
                             */
                6, /* Number of slots. Kept is same as PathORAM */
                1, /* Client and server has same processing speed. Worst case scenario.
                   in general, the server is much faster */
                (1024 * 256), /* 1GB=1024*256 4KB blocks */
                (60 * 60 * 1), /* Client will relax for 60 minutes. In the meantime, the server will keep routing.
                               Assumed, the server processes one edge per second.
                               i.e., 2Z blocks each having 4KB
                               Which turns out to be server processes: 2*6*4KB = 48KB/s */
                two.pow(20) as u64,
            ); /* Experiment runs for 2^29 steps.
               i.e., in this case more than server capacity number of blocks are accessed */

            /* Experiment 2 */
            oram_exp(
                two.pow(26), /* Kept block size 4KB as per other ORAM paper
                                256GB remote storage.
                                2^26*4KB blocks. With compute canada resource cannot simulate larger remote storage
                             */
                6, /* Number of slots. Kept is same as PathORAM */
                1, /* Client and server has same processing speed. Worst case scenario.
                   in general, the server is much faster */
                (12 * 256), /* 12MB=12*256 4KB blocks */
                (5 * 60 * 1), /* Client will relax for 5 minutes. In the meantime, the server will keep routing.
                              Assumed, the server processes one edge per second.
                              i.e., 2Z blocks each having 4KB
                              Which turns out to be server processes: 2*6*4KB = 48KB/s */
                two.pow(20) as u64,
            ); /* Experiment runs for 2^29 steps.
               i.e., in this case more than server capacity number of blocks are accessed */

            /* Experiment 3 */
            oram_exp(
                two.pow(26), /* Kept block size 4KB as per other ORAM paper
                                256GB remote storage.
                                2^26*4KB blocks. With compute canada resource cannot simulate larger remote storage
                             */
                6, /* Number of slots. Kept is same as PathORAM */
                1, /* Client and server has same processing speed. Worst case scenario.
                   in general, the server is much faster */
                (12 * 256), /* 12MB=12*256 4KB blocks */
                (5 * 60 * 1), /* Client will relax for 5 minutes. In the meantime, the server will keep routing.
                              Assumed, the server processes one edge per second.
                              i.e., 2Z blocks each having 4KB
                              Which turns out to be server processes: 2*6*4KB = 48KB/s */
                two.pow(29) as u64,
            ); /* Experiment runs for 2^29 steps.
               i.e., in this case more than server capacity number of blocks are accessed */

            /* Experiment 4 */
            oram_exp(
                two.pow(26), /* Kept block size 4KB as per other ORAM paper
                                256GB remote storage.
                                2^26*4KB blocks. With compute canada resource cannot simulate larger remote storage
                             */
                6, /* Number of slots. Kept is same as PathORAM */
                1, /* Client and server has same processing speed. Worst case scenario.
                   in general, the server is much faster */
                (10240 * 256), /* 10GB=10240*256 4KB blocks */
                (two.pow(29) as u64 - (5 * 60 * 1) as u64) as u64, /* After fetching 10GB data, the client will not access anymore */
                two.pow(29) as u64,
            ); /* Experiment runs for 2^29 steps.
               i.e., in this case more than server capacity number of blocks are accessed */
        }
        experimental_function();
    }
}

/* Implementation of this function not completed.
  It must determine, the timestamp when the current block will be
  available to the leaf bucket.
*/
#[cfg(predicate)]
unsafe fn AvailabilityTS(Tcur: u64, x: u64, w: u64) -> u64 {
    let mut Texp: u64;
    let mut t: u64 = 0;

    let mut lw: u64 = ((w as f64).log2() as u64) + 1; //Automatic floor operation due to type conversion
    let mut ax: u64 = (x >> (L - lw));
    let mut aw: u64 = w; //Ancestor of w, start with w
    let mut prev_aw: u64;

    printdbgln!(0, "level of w({}) is: {}", w, lw);
    printdbgln!(0, "Ancestor of x({}) is: {}", x, ax);

    while (ax != aw) {
        t = t + 2 * (N - 1) - aw - 1;

        if ((aw % 2) == 0) {
            t = t + 1;
        }

        prev_aw = aw;
        ax = ax << 1;
        aw = aw << 1;
    }

    Texp = 0;

    return Texp;
}

/* Observation till date:
- access count of bucket[1] is almost 2/3 of other buckets
- Maximum occupancy of upper buckets are in single digit. Average is very less
  - Maximum occupancy of the upper buckets decreases if the rate increases
- Upper the buffer, average is more. Except the root.
- Bucket[7] has extreamly low average (why?)
- Lower layer buckets have irregular stats
- Lower buckets are accessed less number of times, as expected
- Bucket[15]'s stats are very low
- There are lots of read failure events
- Upper layer buckets goes through more movement and lower layers through less movement
- Leaf buckets have average over 9, why this is happening?
- The maximum of lower buffers are going beyond 26, how to control that?
- For the same rate ratio, maximum value of upper layer buckets changes with N. If N increase, max value is also increasing
- We can think each bucket as a queue, from S. Keshav's video, I learnt that for maintaining a stable situation the arrival rate must be less than
  the departure rate. How to calculate the arrival and departure rates? I can see that the #arrival = #departure as expected
- With the increase of N, write failure increases. N=2^15 failure 57311/50000000. N=2^10: 2960/50000000. N=2^4: 1/50000000.
*/
unsafe fn oram_exp(
    _N: u64,
    _Z: u64,
    _rate_ratio: u64,
    _max_burst_cnt: u64,
    _min_relax_cnt: u64,
    _ITR_CNT: u64,
) {
    /* Set experimentation parameters fist */
    N = _N;
    R = 1;
    Z = _Z; //Number of slots in a bucket
    C = Z / 2;
    rate_ratio = _rate_ratio;
    max_burst_cnt = _max_burst_cnt; //Assume burst size is of 12MB = 12*256 blocks
    min_relax_cnt = _min_relax_cnt; //Assume it is 5 minutes and only 1 edge is processed per second (i.e., 1*2Z*4KB = 48KB/s)

    /* Derived parameters */
    L = ((N as f64).log2() as u64) + 1;
    epoch = 2 * (N - 1);

    /* Local variable */
    ITR_CNT = _ITR_CNT; /* The experiment will run until t reaches itr_cnt */

    let timestamp = Local::now().format("%Y-%m-%d_%H-%M-%S").to_string();
    // Create a folder with the timestamp as its name
    let folder_name = format!("Log_{}", timestamp);
    let folder_path = Path::new(&folder_name);

    match fs::create_dir(folder_path) {
        Ok(_) => {}
        Err(e) => eprintln!("Failed to create folder: {}", e),
    }
    let overall_filename = folder_path.join("Overall_statistics.txt");
    // Handle the Result returned by OpenOptions::new using match
    let mut overallStatFileHandle = match OpenOptions::new()
        .read(true)
        .write(true)
        .create(true) // Create the file if it doesn't exist
        .open(&overall_filename)
    {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Failed to create or open file: {}", e);
            return; // Exit the function if file creation fails
        }
    };

    printdbgln!(1, "ORAM experiment started at: {}", timestamp);

    printdbgln!(
        1,
        "===================================================================================================================
ORAM experiment parameters: N = {}, Z = {}, rate_ratio = {}, max_burst_cnt = {}, min_relax_cnt = {}, ITR_CNT = {}
===================================================================================================================",
        N,
        Z,
        rate_ratio,
        max_burst_cnt,
        min_relax_cnt,
        ITR_CNT
    );

    /* Write to the log file */
    if let Err(e) = writeln!(overallStatFileHandle, "===================================================================================================================
ORAM experiment started at: {}
Parameters: N = {}, Z = {}, rate_ratio = {}, max_burst_cnt = {}, min_relax_cnt = {}, ITR_CNT = {}
===================================================================================================================",
    timestamp,
    N,
    Z,
    rate_ratio,
    max_burst_cnt,
    min_relax_cnt,
    ITR_CNT) {
        eprintln!("Failed to write to file: {}", e);
        return; // Exit the function if writing fails
    }

    let mut tree = &*g_tree;

    /* Initialize the ORAM with dummy data */
    simulate_oram_init(&mut tree);

    tu = 0; /* Initialize with time count 0 */

    /* For synchronization between two threads */
    let (txFrmRoute, rxFrmRoute): (mpsc::Sender<u64>, mpsc::Receiver<u64>) = mpsc::channel();

    // Spawn a new thread to run `clinet_server_interaction()`
    let csi_thread_handle = thread::spawn(|| {
        clinet_server_interaction(rxFrmRoute);
    });

    // Spawn a new thread to run `route()`
    let route_thread_handle = thread::spawn(move || {
        route(txFrmRoute, &mut overallStatFileHandle);
    });

    // Wait for the spawned threads to finish
    route_thread_handle.join().unwrap();
    csi_thread_handle.join().unwrap();

    printdbgln!(
        1,
        "Experimentation ended at: {}",
        Local::now().format("%Y-%m-%d %H:%M:%S.%6f").to_string()
    );
}

unsafe fn clinet_server_interaction(rxFrmRoute: mpsc::Receiver<u64>) {
    //Initialize the randomness
    let mut randomness = rand::thread_rng();
    let mut r_dist = Uniform::new_inclusive(two.pow(L as u32 - 1), (two.pow(L as u32) - 1));
    let mut x_dist = Uniform::new_inclusive(two.pow(L as u32 - 1), (two.pow(L as u32) - 1));
    let mut w_dist = Uniform::new_inclusive(1, (two.pow(L as u32 - 1) - 1));

    /* Do the experiment until a specified time */
    while tu < ITR_CNT {
        /* Wait for signal from the route thread */
        let mut num_pending_access: u64 = 0;
        match rxFrmRoute.recv() {
            Ok(received) => {num_pending_access = received},
            Err(err) => println!("Failed to receive: {}, probably the Route() thread completed", err),
        }

        let mut num_access = 0;

        /* After getting chance, call access(), max_burst_cnt-number of times  */
        while (num_access < num_pending_access) {
            simulate_oram_access(&mut randomness, &mut r_dist, &mut w_dist, &mut x_dist);

            num_access += 1;
        }
    }
}

unsafe fn route(txFrmRoute: mpsc::Sender<u64>, overallStatFileHandle: &mut File) {
    let mut cur_lvl: u64 = 1; //Start with processing level 1
    let mut edges: Vec<(u64, u64)> = Vec::new();

    /* Exit condition is checked within the loop */
    while true {
        printdbgln!(0, "tu: {} Route()", tu as u64);
        /*
          Process edges level by level (level of the upper node).
          At level l, there will be 2^(l-1) nodes, so 2^(l-1) left edges
          and 2^(l-1) right edges.
          For each level first taget to finish all 2^(l-1) left edges,
          which are independent hence CPU level parallelism can be used
          to speed up the simulation.
          Then target the right edges.
          And finishing one level completely, jump to the next level
        */

        /* First process the left edges */
        for label in two.pow(cur_lvl as u32 - 1)..two.pow(cur_lvl as u32) {
            if edges.len() < NumCPUCores!() {
                edges.push((label, (2 * label))); //Left edge
            } else {
                //Process routing in parallel
                let mut do_break =
                    process_pending_edges(&mut edges, &txFrmRoute, overallStatFileHandle);

                if do_break {
                    break;
                }

                edges.push((label, (2 * label)));
            }
        }
        /*
          After execution of the previous loop
          some (2^(l-1)%NumCPUCores!()) will be pending
          process them here and clear the edge queue here
        */
        let mut do_break = process_pending_edges(&mut edges, &txFrmRoute, overallStatFileHandle);

        if do_break {
            break;
        }

        /* Then process the right edges */
        for label in two.pow(cur_lvl as u32 - 1)..two.pow(cur_lvl as u32) {
            if edges.len() < NumCPUCores!() {
                edges.push((label, ((2 * label) + 1)));
            } else {
                //Process routing in parallel
                let mut do_break =
                    process_pending_edges(&mut edges, &txFrmRoute, overallStatFileHandle);

                if do_break {
                    break;
                }

                edges.push((label, ((2 * label) + 1))); //Right edge
            }
        }
        /*
          After execution of the previous loop
          some (2^(l-1)%NumCPUCores!()) will be pending
          process them here and clear the edge queue here
        */
        let mut do_break = process_pending_edges(&mut edges, &txFrmRoute, overallStatFileHandle);

        if do_break {
            break;
        }

        cur_lvl += 1;

        if cur_lvl == L {
            //Start again from the beginning
            cur_lvl = 1;
        }
    }

    /* At the end of the routing, send message to the CSI thread so that CSI thread do now wait forever */
    txFrmRoute.send(0).unwrap();

    oram_print_stat(false, overallStatFileHandle);
}

unsafe fn process_pending_edges(
    edges: &mut Vec<(u64, u64)>,
    txFrmRoute: &mpsc::Sender<u64>,
    overallFile: &mut File,
) -> bool {
    let mut do_break = false;
    let mut num_edge_processed = edges.len() as u64;
    let mut num_pending_access: u64 = 0;

    printdbgln!(
        0,
        "tu: {}, Processing: {:?}, num_edge_processed = {}",
        tu,
        edges,
        num_edge_processed
    );

    //Process routing in parallel
    edges.par_iter().for_each(|(upper, lower)| {
        process_edge(*upper, *lower);
    });
    tu += num_edge_processed;
    since_access += num_edge_processed;
    since_print += num_edge_processed;

    /* Print the partial statistics */
    if since_print >= status_print_freq {
        oram_print_stat(false, overallFile);
        since_print = 0;
    }

    if tu > ITR_CNT {
        do_break = true;
    }

    num_pending_access = (max_burst_cnt * since_access) / (max_burst_cnt + min_relax_cnt);

    if num_pending_access > 0 {
        /* Enable the CSI thread to process access() */
        printdbgln!(
            0,
            "Sending signal for {}-access at since: {}, at tu: {}",
            num_pending_access,
            since_access,
            tu
        );

        txFrmRoute.send(num_pending_access).unwrap();
        since_access = since_access % (max_burst_cnt + min_relax_cnt);
    }

    //Clear the edge queue
    edges.clear();

    return do_break;
}

/* Process an edge of the tree where "upper" is the label of the upper bucket
   and "lower" is the label of the lower bucket of the edge.
*/
unsafe fn process_edge(upper: u64, lower: u64) {
    let mut tree = &*g_tree;

    //At the begining of each processing lock is taken once
    let mut bucketUpper = tree[upper as usize - 1].lock().unwrap();
    let mut bucketLower = tree[lower as usize - 1].lock().unwrap();

    let (mut muUp, mut muDn) = calcMovement(&mut bucketUpper, &mut bucketLower, upper, lower);

    permute(
        &mut bucketUpper,
        &mut bucketLower,
        upper,
        lower,
        &mut muUp,
        &mut muDn,
    );

    //At the end of the function lock on the upper and lower bucket ends
}

unsafe fn simulate_oram_access(
    mut randomness: &mut ThreadRng,
    mut r_dist: &mut Uniform<u64>,
    mut w_dist: &mut Uniform<u64>,
    mut x_dist: &mut Uniform<u64>,
) -> bool {
    let mut success: bool = false;

    let mut tree = &*g_tree;

    printdbg!(0, " Access()");

    /* Perform one read */
    success = simulate_oram_remove(&mut tree, &mut randomness, &mut r_dist);

    /* Perform one write */
    if (success == true) {
        success = simulate_oram_insert(&mut tree, &mut randomness, &mut x_dist, &mut w_dist);
    }

    return success;
}

unsafe fn simulate_oram_insert(
    tree: &Vec<Mutex<Bucket>>,
    mut randomness: &mut ThreadRng,
    mut x_dist: &mut Uniform<u64>,
    mut w_dist: &mut Uniform<u64>,
) -> bool {
    let mut success: bool = false;
    //Randomly select a new leaf node and write node
    let x = randomness.sample(*x_dist);
    let w = randomness.sample(*w_dist);

    let mut bucketW = tree[w as usize - 1].lock().unwrap();

    if (bucketW.occupancy() < Z as usize) {
        //Bucket with label w is stored in location (w-1)
        //Write a block having leaf label x, into the bucket(w)
        bucketW.insert(x, 0, 0); //Last two parameters are dummy now
        bucketW.calc_stat(); //Update statistics
        bucketW.stat.w_cnt += 1;
        bucketW.stat.x_cnt += 1;
        success = true;
    } else {
        /* Cannot write to the block, as it is already full */
        write_failure_cnt += 1;
    }

    return success;
}

unsafe fn simulate_oram_remove(
    tree: &Vec<Mutex<Bucket>>,
    mut randomness: &mut ThreadRng,
    mut r_dist: &mut Uniform<u64>,
) -> bool {
    let mut success: bool = false;
    let mut total_removable: u64 = ((N!()*C) + total_num_placed) - total_num_removed;

    /* Try to remove one block. In the case of failure,
     try unless there is no more buckets available for read */
    while (success == false) && (total_removable > 0){
        //For experiment, remove from each bucket uniformly and in static order
        //Ideally, this parameter must come as an input
        {
            let mut bucket = tree[nxtRdBktLabel as usize - 1].lock().unwrap();

            //Bucket with label r is stored in location (r-1)
            //For experimentation purpose always read the first item from the bucket
            //Ideally, the client must only remove the requested block
            if (bucket.occupancy() > 0) {
                bucket.removeNxt();
                bucket.calc_stat(); //Update statistics
                bucket.stat.r_cnt += 1;
                total_num_removed += 1;
                success = true;
            }

            nxtRdBktLabel += 1;
            /* Wrap around */
            if (nxtRdBktLabel > (two.pow(L as u32) - 1)){
                nxtRdBktLabel = two.pow(L as u32 - 1);
            }
        }
    }

    if success == false {
        read_underflow_cnt += 1; //In real scenario, this will not happen unless the server misbehaves. Because, the client will not issue read in that case.
    }

    return  success;

}

unsafe fn simulate_oram_remove_old(
    tree: &Vec<Mutex<Bucket>>,
    mut randomness: &mut ThreadRng,
    mut r_dist: &mut Uniform<u64>,
) -> bool {
    let mut success: bool = true;
    //For experiment, randomly select a leaf node to remove.
    //Ideally, this parameter must come as an input
    let r = randomness.sample(*r_dist);
    let mut bucket = tree[r as usize - 1].lock().unwrap();
    //Bucket with label r is stored in location (r-1)
    //For experimentation purpose always read the first item from the bucket
    //Ideally, the client must only remove the requested block
    if (bucket.occupancy() > 0) {
        bucket.removeNxt();
        bucket.calc_stat(); //Update statistics
        bucket.stat.r_cnt += 1;
        total_num_removed += 1;
    } else {
        read_underflow_cnt += 1; //In real scenario, this will not happen unless the server misbehaves. Because, the client will not issue read in that case.
        success = false;
    }
    return success;
}

unsafe fn simulate_oram_init(tree: &Vec<Mutex<Bucket>>) {
    for x in two.pow(L as u32 - 1)..=(two.pow(L as u32) - 1) {
        {
            let mut bucket = tree[x as usize - 1].lock().unwrap();
            /* Insert C number of replicas, in each replica the same address is specified */
            for i in 0..C {
                bucket.insert(x, 0, 0); /* Last two parameters are dummy now */
            }
            bucket.calc_stat();
        } //Mutex guard for each bucket ends here
    }

    /* At first the read must be from the first leaf */
    nxtRdBktLabel = two.pow(L as u32 - 1);    
}

unsafe fn oram_print_stat(print_details: bool, overallFile: &mut File) {
    let mut simulation_percentage: f64;
    let mut read_underflow_percentage: f64;
    let mut placement_percentage: f64;

    let timestamp = Local::now().format("%Y-%m-%d_%H:%M:%S").to_string();

    #[cfg(any())]
    {
        let mut detailedFile: File;
        let detailed_filename = folder_path.join("detailed_log.csv");

        if print_details {
            // Handle the Result returned by File::create using match
            detailedFile = match File::create(&detailed_filename) {
                Ok(f) => f,
                Err(e) => {
                    eprintln!("Failed to create file: {}", e);
                    return; // Exit the function if file creation fails
                }
            };

            // Handle the Result returned by writeln! using match
            if let Err(e) = writeln!(detailedFile, "Bucket,a_cnt,r_cnt,w_cnt,x_cnt,cur_occupancy,avg,var,max,out_up,out_lft,out_rgt,in_up,in_lft,in_rgt,sty") {
            eprintln!("Failed to write to file: {}", e);
            return; // Exit the function if writing fails
        }

            for b in 1..=(two.pow(L) - 1) {
                tree[b as usize - 1].print_detailed_stat(&mut detailedFile);
            }

            /* Note: We are not calculating read error. i.e., the block must be availabel at some leaf but is not.
             Basically, if the server is honest(but curious) then that value must be zero, if routing_congestion_cnt = 0
            */
            let mut congested_buckets = g_congested_buckets.lock().unwrap();
        }
    }

    write_failure_percentage =
        ((write_failure_cnt * 100) as f64 / (write_failure_cnt + total_num_removed) as f64);
    routing_congestion_percentage = ((routing_congestion_cnt.load(Ordering::SeqCst) * 100) as f64 / (tu + 1) as f64);

    simulation_percentage = (((tu + 1) * 100) as f64 / ITR_CNT as f64);
    read_underflow_percentage =
        (((read_underflow_cnt) * 100) as f64 / (read_underflow_cnt + total_num_removed) as f64);
    placement_percentage = (((total_num_placed) * 100) as f64 / total_num_removed as f64);

    if clrOld {
        // ANSI escape code to move the cursor up 8 lines
        print!("\x1b[9A");

        // ANSI escape code to clear from cursor to end of screen
        print!("\x1b[J");

        // Flush stdout to apply changes
        std::io::stdout().flush().unwrap();

        // Read the entire file into a string
        let mut content = String::new();
        // Move the cursor back to the begining of the file
        overallFile.seek(SeekFrom::Start(0));
        overallFile.read_to_string(&mut content);

        // Split the content by lines and collect them
        let mut lines: Vec<&str> = content.lines().collect();

        // Remove the last 9 lines
        lines.truncate(lines.len() - 9);

        // Join the remaining lines back together
        let new_content = lines.join("\n") + "\n";

        // Truncate the file and write the new content
        overallFile.set_len(0); // Clear the file
        overallFile.seek(SeekFrom::Start(0)); // Move the cursor to the start
        overallFile.write_all(new_content.as_bytes());
        overallFile.flush();

        // Read the entire file into a string
        let mut content1 = String::new();
        // Move the cursor back to the begining of the file
        overallFile.seek(SeekFrom::Start(0));
        overallFile.read_to_string(&mut content1);

        // Split the content by lines and collect them
        let mut lines1: Vec<&str> = content1.lines().collect();
    }

    /* From the second time onwards, it will be set */
    clrOld = true;

    printdbgln!(
        1,
        "**** Last updated at: {}, {} % simulation done (tu = {} out of {}), current statistics is:
-----------------------------------------------------------------------------------------------------------------------
Read underflow count: {}({} %)
Write failure count: {}({} %)
Routing congestion count: {}({} %)
Global max load: {}
Total number of removals: {}
Total number of placements: {}({} %)
Last placement occurred at: {}",
        timestamp,
        simulation_percentage.ceil(),
        tu + 1,
        ITR_CNT,        
        read_underflow_cnt,
        read_underflow_percentage,
        write_failure_cnt,
        write_failure_percentage,
        routing_congestion_cnt.load(Ordering::SeqCst),
        routing_congestion_percentage,
        global_max_bucket_load,
        total_num_removed,
        total_num_placed,
        placement_percentage,
        last_placement_tu
    );

    if let Err(e) = writeln!(
        overallFile,
        "**** Last updated at: {}, {} % simulation done (tu = {} out of {}), current statistics is:
-----------------------------------------------------------------------------------------------------------------------
Read underflow count: {}({} %)
Write failure count: {}({} %)
Routing congestion count: {}({} %)
Global max load: {}
Total number of removals: {}
Total number of placements: {}({} %)
Last placement occurred at: {}",
        timestamp,
        simulation_percentage.ceil(),
        tu + 1,
        ITR_CNT,        
        read_underflow_cnt,
        read_underflow_percentage,
        write_failure_cnt,
        write_failure_percentage,
        routing_congestion_cnt.load(Ordering::SeqCst),
        routing_congestion_percentage,
        global_max_bucket_load,
        total_num_removed,
        total_num_placed,
        placement_percentage,
        last_placement_tu
    ) {
        eprintln!("Failed to write to file: {}", e);
        return; // Exit the function if writing fails
    }
}

unsafe fn calcMovement(
    bucketUpper: &mut Bucket,
    bucketLower: &mut Bucket,
    upper: u64,
    lower: u64,
) -> (Vec<i32>, Vec<i32>) {
    let mut l_upper: u64 = ((upper as f64).log2() as u64) + 1;
    let mut l_lower: u64 = l_upper + 1;

    let mut muUp = Vec::new();
    let mut muDn = Vec::new();
    /* First upper bucket */
    for i in 0..Z {
        if bucketUpper.blocks[i as usize].m.x == 0 {
            muUp.push(EMPTY!());
        } else {
            if (lower == (bucketUpper.blocks[i as usize].m.x >> (L - l_lower))) {
                muUp.push(MOVE!());
            } else {
                muUp.push(NOT_MOVE!());
            }
        }
    }
    /* Then check the lower bucket */
    for i in 0..Z {
        if bucketLower.blocks[i as usize].m.x == 0 {
            muDn.push(EMPTY!());
        } else {
            if (lower == (bucketLower.blocks[i as usize].m.x >> (L - l_lower))) {
                muDn.push(NOT_MOVE!());
            } else {
                muDn.push(MOVE!());
            }
        }
    }

    (muUp, muDn)
}

/* Inspired from the movement algorithm in sumit_draft.docx not according to the paper */
unsafe fn permute(
    bucketUpper: &mut Bucket,
    bucketLower: &mut Bucket,
    upper: u64,
    lower: u64,
    muUp: &mut Vec<i32>,
    muDn: &mut Vec<i32>,
) {
    let mut congestion: bool = false;

    /* First swap */
    for i in 0..Z as usize {
        for j in 0..Z as usize {
            if (muUp[i] == MOVE!()) && (muDn[j] == MOVE!()) {
                let tmp: blk = bucketUpper.blocks[i].clone();
                bucketUpper.blocks[i].m.x = bucketLower.blocks[j].m.x;
                bucketLower.blocks[j] = tmp;
                muUp[i] = NOT_MOVE!();
                muDn[j] = NOT_MOVE!();

                /* Track movements of the lower bucket */
                bucketLower.stat.in_up_cnt += 1; //One block came from upper bucket and one went to upper
                bucketLower.stat.out_up_cnt += 1; //One block went to the upper bucket

                /* Track movements of the upper bucket */
                if lower % 2 == 0 {
                    /* Lower bucket is a left child */
                    bucketUpper.stat.in_lft_cnt += 1; //One block came from left child
                    bucketUpper.stat.out_lft_cnt += 1; //One block went to the left child
                } else {
                    bucketUpper.stat.in_rgt_cnt += 1; //One block came from right child
                    bucketUpper.stat.out_rgt_cnt += 1; //One block went to the right child
                }
                /*
                 Swapping cannot happen for leaf nodes,
                 because no block should go up from a leaf node
                 so, placement count is not required to update here
                */
            }
        }
    }

    /* Move up */
    for i in 0..Z as usize {
        for j in 0..Z as usize {
            if (muUp[j] == EMPTY!()) && (muDn[i] == MOVE!()) {
                bucketUpper.blocks[j].m.x = bucketLower.blocks[i].m.x;
                bucketLower.blocks[i].m.x = 0;
                muUp[j] = NOT_MOVE!();
                muDn[i] = EMPTY!();

                /* Track movements of the lower bucket */
                bucketLower.stat.out_up_cnt += 1; //One block went to the upper bucket

                /* Track movements of the upper bucket */
                if lower % 2 == 0 {
                    /* Lower bucket is a left child */
                    bucketUpper.stat.in_lft_cnt += 1; //One block came from left child
                } else {
                    bucketUpper.stat.in_rgt_cnt += 1; //One block came from right child
                }
                /* No block can be moved to the leaf,
                during the upward movement */
            }
        }
    }

    /* Move down */
    for i in 0..Z as usize {
        for j in 0..Z as usize {
            if (muUp[i] == MOVE!()) && (muDn[j] == EMPTY!()) {
                bucketLower.blocks[j].m.x = bucketUpper.blocks[i].m.x;
                bucketUpper.blocks[i].m.x = 0;
                muUp[i] = EMPTY!();
                muDn[j] = NOT_MOVE!();

                /* Track movements of the lower bucket */
                bucketLower.stat.in_up_cnt += 1; //One block came from the upper bucket

                /* Track movements of the upper bucket */
                if lower % 2 == 0 {
                    /* Lower bucket is a left child */
                    bucketUpper.stat.out_lft_cnt += 1; //One block went to the left child
                } else {
                    bucketUpper.stat.out_rgt_cnt += 1; //One block went to the right child
                }

                /* Means routing process is able to return back
                one block to its destined leaf bucket */
                if (bucketLower.blocks[j].m.x == lower) {
                    total_num_placed += 1;
                    last_placement_tu = tu;
                }
            }
        }
    }

    /* Update block statistics */
    bucketLower.calc_stat();
    bucketUpper.calc_stat();

    /* After performing permutation, check congestion */
    for i in 0..Z as usize {
        //let mut congested_buckets = g_congested_buckets.lock().unwrap();
        /* Ideally there should not be any movable block in either bucket */
        if (muUp[i] == MOVE!()) {
            num_congestion_blocks += 1; //This is to be done within lock

            /*
            Still some blocks in the upper bucket remains unmoved
              Means, the lower bucket is full and congested
            */
            //congested_buckets.push(lower);
            congestion = true;
        }
        if (muDn[i] == MOVE!()) {
            num_congestion_blocks += 1;

            /*
            Still some blocks in the lower bucket remains unmoved
              Means, the upper bucket is full and congested
            */
            //congested_buckets.push(upper);
            congestion = true;
        }
    }

    if congestion {
        //routing_congestion_cnt += 1; //This is to be done within lock
        routing_congestion_cnt.fetch_add(1, Ordering::SeqCst);
    }
}

unsafe fn experimental_function() {
    let mut total_sim_steps: u64 = two.pow(36) as u64; //22 Working
    let mut burst_cnt: u64 = 1; //two.pow(6) as u64;
    let mut relax_cnt = 1000; //u64 = two.pow() as u64;
                            /* Unexpectedly, relax_cnt = 500 gives 3% congestion, whereas relax_cnt = 50 gives 0.61%
                               The reason is, for relax_cnt = 50, there is a high read underflow
                               hence, the effective relax count becomes quite less
                            */
    status_print_freq = two.pow(27) as u64;

    oram_exp(
        N!(), //11 working//15 means 2^15*4KB blocks = 2^15*2^12 = 2^27 = 128MB
        40,
        1,
        (burst_cnt),     /* Only access few elements at the beginnig */
        (relax_cnt),     /* Then perform nothing for rest of the time */
        total_sim_steps, //total_sim_steps/_N should be 2^11?
    );
}