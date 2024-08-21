use tfhe::boolean::backward_compatibility::client_key;
use tfhe::integer::bigint::U1024;
use tfhe::prelude::*;
use tfhe::{
    generate_keys, set_server_key, ConfigBuilder, FheBool, FheInt32, FheUint, FheUint1024,
    FheUint1024Id,
};
extern crate chrono;
use chrono::Local;
use once_cell::sync::Lazy;
use rand::distributions::{Distribution, Uniform};
use rand::rngs::ThreadRng;
use rand::Rng;
use rayon::prelude::*;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::fs;
use std::fs::File;
use std::io::{BufWriter, Result};
use std::io::Write;
use std::mem::MaybeUninit;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::sync::Mutex;
use std::thread;
use tfhe::prelude::*;
use tfhe::ClientKey;
use std::fs::{OpenOptions};
use std::io::{Read, Seek, SeekFrom};

// Define a global mutable list (vector) wrapped in a Mutex for thread safety
static g_congested_buckets: Lazy<Mutex<Vec<u32>>> = Lazy::new(|| Mutex::new(vec![]));
static g_tree: Lazy<Mutex<Vec<Bucket>>> = Lazy::new(|| Mutex::new(vec![]));

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
static mut N: u32 = 8;
static mut L: u32 = 4;
static mut R: u32 = 1;
static mut C: u32 = 1; /* Initial number of replicas */
static mut Z: u32 = 8;
static mut B: u32 = 4096; /* Common block size is: 4KB
                          But RLWE can encrypt 3KB per ciphertext.
                          So, block size must be set to multiple of 3KB.
                          Moreover, some place must be kept reserved for storing metadata */
static mut epoch: u32 = 14; //2(N-1)
static mut ITR_CNT: u64 = 1024; /* The experiment will run for this amount of time */
static mut rate_ratio: u32 = 10; //Ratio of server's processing : Client's processing
static mut two: u32 = 2;
static mut tu: u64 = 0; /* Count of time unit */
static mut read_underflow_cnt: u64 = 0; /* The number of times the read operation failed */
static mut write_failure_cnt: u64 = 0; /* The number of times the write operation failed */
static mut write_failure_percentage: f64 = 0.0; /* The percentage of failed write operation */
static mut routing_congestion_cnt: u64 = 0; /* The number of times the background operation caused buffer overflow */
static mut routing_congestion_percentage: f64 = 0.0; /* The percentage of congested steps during routing */
static mut num_congestion_blocks: u64 = 0; /* The number of blocks affected due to congestion */
static mut max_burst_cnt: u64 = 0; /* The number of blocks the client retrives in a burst */
static mut min_relax_cnt: u64 = 0; /* The amount of time (in terms of step processing), the client relaxes after each burst */
static mut global_max_bucket_load: u32 = 0; /* Maximum load occurred in any bucket */
static mut total_num_removed: u64 = 0; /* Total number of blocks removed from its leaf location */
static mut total_num_placed: u64 = 0; /* How many number of blocks are returned to place by the routing process */
static mut last_placement_tu: u64 = 0; /* When the last block is placed to its destined leaf */
static mut clrOld: bool = false; /* Clear previous prints */

#[derive(Debug)]
struct m {
    a: u32,
    x: u32,
}
#[derive(Debug)]
struct blk {
    m: m,
    //d: Vec<FheUint<FheUint1024Id>>,
    d: u32,
}

struct Bucket {
    b: u32,           //The label of this bucket
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
    max: u32,
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
    fn new(id: u32, lf: u32) -> Self {
        blk {
            m: m { a: 0, x: 0 },
            //d: Vec::new(),
            d: 0 as u32,
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
    unsafe fn new(label: u32) -> Self {
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

    // Method to add a u32(which contains the metadata m.x) in the place of 0
    unsafe fn insert(&mut self, x: u32, a: u32, d: u32) -> bool {
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
    unsafe fn removeNxt(&mut self) -> u32 {
        let mut removed_item: u32 = 0;

        for slot in 0..Z as usize {
            if self.blocks[slot].m.x != 0 {
                removed_item = self.blocks[slot].d;
                self.blocks[slot].m.x = 0;//Mark the slot as empty
                break;
            }
        }

        return removed_item;
    }

    // Method to remove an item from the stated index and insert 0 in that place
    fn remove(&mut self, index: usize) -> u32 {
        let mut removed_item: u32 = self.blocks[index].d;
        self.blocks[index].m.x = 0;

        return removed_item;
    }

    // Method to remove an item by its value
    /*
    fn removeVal(&mut self, value: u32) -> u32 {
        let mut removed_item: u32 = 0;

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

        let mut current: u32 = self.occupancy() as u32;
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

    let mut Tcur: u32;
    let mut x: u32;
    let mut w: u32;

    unsafe {
        Tcur = 0;
        let mut rng = rand::thread_rng();
        x = rng.gen_range(two.pow(L - 1)..(two.pow(L) - 1));
        w = rng.gen_range(1..(two.pow(L - R) - 1));

        x = rng.gen_range(two.pow(L - 1)..(two.pow(L) - 1));
        w = rng.gen_range(1..(two.pow(L - R) - 1));

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
unsafe fn AvailabilityTS(Tcur: u32, x: u32, w: u32) -> u32 {
    let mut Texp: u32;
    let mut t: u32 = 0;

    let mut lw: u32 = ((w as f64).log2() as u32) + 1; //Automatic floor operation due to type conversion
    let mut ax: u32 = (x >> (L - lw));
    let mut aw: u32 = w; //Ancestor of w, start with w
    let mut prev_aw: u32;

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
    _N: u32,
    _Z: u32,
    _rate_ratio: u32,
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
    L = ((N as f64).log2() as u32) + 1;
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
        .create(true)  // Create the file if it doesn't exist
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
ORAM experiment parameters: N = {}, Z = {}, rate_ratio = {}, max_burst_cnt = {}, min_relax_cnt = {}, ITR_CNT = {}
===================================================================================================================",
    N,
    Z,
    rate_ratio,
    max_burst_cnt,
    min_relax_cnt,
    ITR_CNT) {
        eprintln!("Failed to write to file: {}", e);
        return; // Exit the function if writing fails
    }

    {
        let mut tree = g_tree.lock().unwrap();
        /* Loop from 1 to 2N - 1 */
        for i in 1..=(2 * (N as usize) - 1) {
            tree.push(Bucket::new(i as u32));
        }

        /* Initialize the ORAM with dummy data */
        simulate_oram_init(&mut tree);
    } /* Mutex automatically unlocked here */

    tu = 0; /* Initialize with time count 0 */

    /* For synchronization between two threads */
    let (txFrmRoute, rxFrmRoute): (mpsc::Sender<bool>, mpsc::Receiver<bool>) = mpsc::channel();
    let (txFrmCsi, rxFrmCsi): (mpsc::Sender<bool>, mpsc::Receiver<bool>) = mpsc::channel();

    // Spawn a new thread to run `clinet_server_interaction()`
    let csi_thread_handle = thread::spawn(|| {
        clinet_server_interaction(txFrmCsi, rxFrmRoute);
    });

    // Spawn a new thread to run `route()`
    let route_thread_handle = thread::spawn(move || {
        route(txFrmRoute, rxFrmCsi, &mut overallStatFileHandle);
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

unsafe fn clinet_server_interaction(
    txFrmCsi: mpsc::Sender<bool>,
    rxFrmRoute: mpsc::Receiver<bool>,
) {
    let mut cur_burst_cnt = 0;
    let mut relax_cnt = 0;
    //Initialize the randomness
    let mut randomness = rand::thread_rng();
    let mut r_dist = Uniform::new_inclusive(two.pow(L - 1), (two.pow(L) - 1));
    let mut x_dist = Uniform::new_inclusive(two.pow(L - 1), (two.pow(L) - 1));
    let mut w_dist = Uniform::new_inclusive(1, (two.pow(L - 1) - 1));

    /* Do the experiment until a specified time */
    while tu < ITR_CNT {
        let _ = rxFrmRoute.recv();
        if (cur_burst_cnt < max_burst_cnt) {
            simulate_oram_access(&mut randomness, &mut r_dist, &mut w_dist, &mut x_dist);

            cur_burst_cnt += 1;
        } else {
            if (relax_cnt < min_relax_cnt) {
                relax_cnt = (relax_cnt + 1) % min_relax_cnt;

                if (relax_cnt == 0) {
                    cur_burst_cnt = 0;
                }
            }
        }

        /* After doing access, disabling it
          Again it will be enabled from route()
        */
        txFrmCsi.send(true);
    }
}

unsafe fn route(
    txFrmRoute: mpsc::Sender<bool>,
    rxFrmCsi: mpsc::Receiver<bool>,
    overallStatFileHandle: &mut File,
) {
    let mut node_que: VecDeque<u32> = VecDeque::new(); /* Queue of parent nodes */
    let mut process_left_edge: bool = true;
    let mut lower: u32;
    let mut locked_steps: u32;    

    node_que.push_front(1); /* At first push the root bucket. Located in tree[0], but has label = 1 */

    //CSI thread is waiting, so at the beginning send a dummy start message to the CSI thread
    txFrmRoute.send(true);

    /* Run the thread until the specified time */
    while tu < ITR_CNT {
        let _ = rxFrmCsi.recv();

        let mut tree = g_tree.lock().unwrap();
        locked_steps = 0;

        while locked_steps < rate_ratio {
            printdbgln!(0, "tu: {} Route()", tu + locked_steps as u64);

            /* During each step, two different edges are processed */
            if let Some(upper) = node_que.pop_back() {
                if process_left_edge {
                    lower = 2 * upper;
                    node_que.push_back(upper); /* As left edge is being processed, it will again come as upper node */
                } else {
                    lower = 2 * upper + 1;
                }

                let (mut muUp, mut muDn) = calcMovement(&mut tree, upper, lower);

                permute(&mut tree, upper, lower, &mut muUp, &mut muDn);
                locked_steps += 1;

                node_que.push_front(lower);
            } else {
                printdbgln!(1, "Queue is empty, should not come here..!!");
            }

            /* Re-initialize the queue */
            if ((tu + locked_steps as u64) % (epoch as u64)) == 0 {
                //epoch is global variable
                node_que.clear();
                node_que.push_front(1);
            }

            /* Print the partial statistics */
            if (tu + locked_steps as u64 + 1) % (ITR_CNT / 10) == 0 {
                oram_print_stat(false, overallStatFileHandle);
            }

            /*
              If current iteration processes left edge,
              then the next iteration will process the right edge and vice-versa.
            */
            process_left_edge = !process_left_edge;
        }

        /* As inner loop executed for rate_ratio steps, increament tu accordingly */
        tu += rate_ratio as u64;

        /*
          Mutex automatically unlocked here.
          So, before the next starting of the inner loop
          access() gets a chance to execute.
        */

        /* Enable the client server to process access() */
        txFrmRoute.send(true);
    }
}

unsafe fn simulate_oram_access(
    mut randomness: &mut ThreadRng,
    mut r_dist: &mut Uniform<u32>,
    mut w_dist: &mut Uniform<u32>,
    mut x_dist: &mut Uniform<u32>,
) -> bool {
    let mut success: bool = false;

    let mut tree = g_tree.lock().unwrap();

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
    tree: &mut Vec<Bucket>,
    mut randomness: &mut ThreadRng,
    mut x_dist: &mut Uniform<u32>,
    mut w_dist: &mut Uniform<u32>,
) -> bool {
    let mut success: bool = false;
    //Randomly select a new leaf node and write node
    let x = randomness.sample(*x_dist);
    let w = randomness.sample(*w_dist);

    if (tree[w as usize - 1].occupancy() < Z as usize) {
        //Bucket with label w is stored in location (w-1)
        //Write a block having leaf label x, into the bucket(w)
        tree[w as usize - 1].insert(x, 0, 0); //Last two parameters are dummy now
        tree[w as usize - 1].calc_stat(); //Update statistics
        tree[w as usize - 1].stat.w_cnt += 1;
        tree[x as usize - 1].stat.x_cnt += 1;
        success = true;
    } else {
        /* Cannot write to the block, as it is already full */
        write_failure_cnt += 1;
    }

    return success;
}

unsafe fn simulate_oram_remove(
    tree: &mut Vec<Bucket>,
    mut randomness: &mut ThreadRng,
    mut r_dist: &mut Uniform<u32>,
) -> bool {
    let mut success: bool = true;

    //For experiment, randomly select a leaf node to remove.
    //Ideally, this parameter must come as an input
    let r = randomness.sample(*r_dist);

    //Bucket with label r is stored in location (r-1)
    //For experimentation purpose always read the first item from the bucket
    //Ideally, the client must only remove the requested block
    if (tree[r as usize - 1].occupancy() > 0) {
        tree[r as usize - 1].removeNxt();
        tree[r as usize - 1].calc_stat(); //Update statistics
        tree[r as usize - 1].stat.r_cnt += 1;
        total_num_removed += 1;
    } else {
        read_underflow_cnt += 1; //In real scenario, this will not happen unless the server misbehaves. Because, the client will not issue read in that case.
        success = false;
    }

    return success;
}

unsafe fn simulate_oram_init(tree: &mut Vec<Bucket>) {
    for x in two.pow(L - 1)..=(two.pow(L) - 1) {
        /* Insert C number of replicas, in each replica the same address is specified */
        for i in 0..C {
            tree[x as usize - 1].insert(x, 0, 0); /* Last two parameters are dummy now */
        }
        tree[x as usize - 1].calc_stat();
    }
}

unsafe fn oram_print_stat(print_details: bool, overallFile: &mut File) {
    let mut simulation_percentage: f64;
    let mut read_underflow_percentage: f64;
    let mut placement_percentage: f64;

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
    routing_congestion_percentage = ((routing_congestion_cnt * 100) as f64 / (tu+1) as f64);

    simulation_percentage = (((tu+1) * 100) as f64 / ITR_CNT as f64);
    read_underflow_percentage = (((read_underflow_cnt) * 100) as f64 / (read_underflow_cnt + total_num_removed) as f64);
    placement_percentage = (((total_num_placed) * 100) as f64 / total_num_removed as f64);

    if clrOld {
        // ANSI escape code to move the cursor up 8 lines
        print!("\x1b[8A");

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

    // Remove the last n lines
    lines.truncate(lines.len() - 8);

    // Join the remaining lines back together
    let new_content = lines.join("\n")+"\n";

    // Truncate the file and write the new content
    overallFile.set_len(0);  // Clear the file
    overallFile.seek(SeekFrom::Start(0));  // Move the cursor to the start
    overallFile.write_all(new_content.as_bytes());
    overallFile.flush();

    // Read the entire file into a string
    let mut content1 = String::new();
    // Move the cursor back to the begining of the file
    overallFile.seek(SeekFrom::Start(0));
    overallFile.read_to_string(&mut content1);

    // Split the content by lines and collect them
    let mut lines1: Vec<&str> = content1.lines().collect();
    print!("After update: {}, number of lines: {}", content1.len(), lines1.len());

    }

    /* From the second time onwards, it will be set */
    clrOld = true;

    printdbgln!(
        1,
        "**** Simulation done: {} %, current statistics =>
Read underflow count: {}({} %)
Write failure count: {}({} %)
Routing congestion count: {}({} %)
Global max load: {}
Total number of removals: {}
Total number of placements: {}({} %)
Last placement occurred at: {}",
        simulation_percentage.ceil(),
        read_underflow_cnt,
        read_underflow_percentage,
        write_failure_cnt,
        write_failure_percentage,
        routing_congestion_cnt,
        routing_congestion_percentage,
        global_max_bucket_load,
        total_num_removed,
        total_num_placed,
        placement_percentage,
        last_placement_tu
    );

    if let Err(e) = writeln!(
        overallFile,
        "**** Simulation done: {} %, current statistics =>
Read underflow count: {}({} %)
Write failure count: {}({} %)
Routing congestion count: {}({} %)
Global max load: {}
Total number of removals: {}
Total number of placements: {}({} %)
Last placement occurred at: {}",
        simulation_percentage.ceil(),
        read_underflow_cnt,
        read_underflow_percentage,
        write_failure_cnt,
        write_failure_percentage,
        routing_congestion_cnt,
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

unsafe fn calcMovement(tree: &mut Vec<Bucket>, upper: u32, lower: u32) -> (Vec<i32>, Vec<i32>) {
    let mut l_upper: u32 = ((upper as f64).log2() as u32) + 1;
    let mut l_lower: u32 = l_upper + 1;

    #[cfg(all())]
    {
        let mut muUp = Vec::new();
        let mut muDn = Vec::new();
        /* First upper bucket */
        for i in 0..Z {
            if tree[upper as usize - 1].blocks[i as usize].m.x == 0 {
                muUp.push(EMPTY!());
            } else {
                if (lower == (tree[upper as usize - 1].blocks[i as usize].m.x >> (L - l_lower))) {
                    muUp.push(MOVE!());
                } else {
                    muUp.push(NOT_MOVE!());
                }
            }
        }
        /* Then check the lower bucket */
        for i in 0..Z {
            if tree[lower as usize - 1].blocks[i as usize].m.x == 0 {
                muDn.push(EMPTY!());
            } else {
                if (lower == (tree[lower as usize - 1].blocks[i as usize].m.x >> (L - l_lower))) {
                    muDn.push(NOT_MOVE!());
                } else {
                    muDn.push(MOVE!());
                }
            }
        }

        (muUp, muDn)
    }

    #[cfg(any())]{
    /* CPU level parrallelism is used to enhance the simulation speed */
    /* At first analyze the upper bucket */
    let muUp: Vec<_> = (0..Z)
        .into_par_iter()
        .map(|i| {
            let block = &tree[upper as usize - 1].blocks[i as usize];

            if block.m.x == 0 {
                EMPTY!() // Push EMPTY
            } else {
                if lower == (block.m.x >> (L - l_lower)) {
                    MOVE!() // Push MOVE
                } else {
                    NOT_MOVE!() // Push NOT_MOVE
                }
            }
        })
        .collect(); // Collect all results into a vector

    /* Then analyze the lower bucket */
    let muDn: Vec<_> = (0..Z)
        .into_par_iter()
        .map(|i| {
            let block = &tree[lower as usize - 1].blocks[i as usize];

            if block.m.x == 0 {
                EMPTY!() // Push EMPTY
            } else {
                if lower == (block.m.x >> (L - l_lower)) {
                    NOT_MOVE!() // Push NOT_MOVE
                } else {
                    MOVE!() // Push MOVE
                }
            }
        })
        .collect(); // Collect all results into a vector
    
        (muUp, muDn)
    }
}

/* Inspired from the movement algorithm in sumit_draft.docx not according to the paper */
unsafe fn permute(
    tree: &mut Vec<Bucket>,
    upper: u32,
    lower: u32,
    muUp: &mut Vec<i32>,
    muDn: &mut Vec<i32>,
) {
    let mut l_lower: u32 = ((lower as f64).log2() as u32) + 1;
    let mut congestion: bool = false;

    //printdbgln!(1, "Routing: {}<->{}", upper, lower);

    /* First swap */
    for i in 0..Z as usize {
        for j in 0..Z as usize {
            if (muUp[i] == MOVE!()) && (muDn[j] == MOVE!()) {
                let tmp: blk = tree[upper as usize - 1].blocks[i].clone();
                tree[upper as usize - 1].blocks[i].m.x = tree[lower as usize - 1].blocks[j].m.x;
                tree[lower as usize - 1].blocks[j] = tmp;
                muUp[i] = NOT_MOVE!();
                muDn[j] = NOT_MOVE!();

                /* Track movements of the lower bucket */
                tree[lower as usize - 1].stat.in_up_cnt += 1; //One block came from upper bucket and one went to upper
                tree[lower as usize - 1].stat.out_up_cnt += 1; //One block went to the upper bucket

                /* Track movements of the upper bucket */
                if lower % 2 == 0 {
                    /* Lower bucket is a left child */
                    tree[upper as usize - 1].stat.in_lft_cnt += 1; //One block came from left child
                    tree[upper as usize - 1].stat.out_lft_cnt += 1; //One block went to the left child
                } else {
                    tree[upper as usize - 1].stat.in_rgt_cnt += 1; //One block came from right child
                    tree[upper as usize - 1].stat.out_rgt_cnt += 1; //One block went to the right child
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
                tree[upper as usize - 1].blocks[j].m.x = tree[lower as usize - 1].blocks[i].m.x;
                tree[lower as usize - 1].blocks[i].m.x = 0;
                muUp[j] = NOT_MOVE!();
                muDn[i] = EMPTY!();

                /* Track movements of the lower bucket */
                tree[lower as usize - 1].stat.out_up_cnt += 1; //One block went to the upper bucket

                /* Track movements of the upper bucket */
                if lower % 2 == 0 {
                    /* Lower bucket is a left child */
                    tree[upper as usize - 1].stat.in_lft_cnt += 1; //One block came from left child
                } else {
                    tree[upper as usize - 1].stat.in_rgt_cnt += 1; //One block came from right child
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
                tree[lower as usize - 1].blocks[j].m.x = tree[upper as usize - 1].blocks[i].m.x;
                tree[upper as usize - 1].blocks[i].m.x = 0;
                muUp[i] = EMPTY!();
                muDn[j] = NOT_MOVE!();

                /* Track movements of the lower bucket */
                tree[lower as usize - 1].stat.in_up_cnt += 1; //One block came from the upper bucket

                /* Track movements of the upper bucket */
                if lower % 2 == 0 {
                    /* Lower bucket is a left child */
                    tree[upper as usize - 1].stat.out_lft_cnt += 1; //One block went to the left child
                } else {
                    tree[upper as usize - 1].stat.out_rgt_cnt += 1; //One block went to the right child
                }

                /* Means routing process is able to return back
                one block to its destined leaf bucket */
                if (tree[lower as usize - 1].blocks[j].m.x == lower) {
                    total_num_placed += 1;
                    last_placement_tu = tu;
                }
            }
        }
    }

    /* Update block statistics */
    tree[lower as usize - 1].calc_stat();
    tree[upper as usize - 1].calc_stat();

    /* After performing permutation, check congestion */
    for i in 0..Z as usize {
        let mut congested_buckets = g_congested_buckets.lock().unwrap();
        /* Ideally there should not be any movable block in either bucket */
        if (muUp[i] == MOVE!()) {
            num_congestion_blocks += 1;

            /*
            Still some blocks in the upper bucket remains unmoved
              Means, the lower bucket is full and congested
            */
            congested_buckets.push(lower);
            congestion = true;
        }
        if (muDn[i] == MOVE!()) {
            num_congestion_blocks += 1;

            /*
            Still some blocks in the lower bucket remains unmoved
              Means, the upper bucket is full and congested
            */
            congested_buckets.push(upper);
            congestion = true;
        }
    }

    if congestion {
        routing_congestion_cnt += 1;
    }
}

unsafe fn experimental_function() {
    let mut total_sim_steps: u64 = two.pow(27) as u64; //22 Working
    let mut burst_cnt: u64 = 50; //two.pow(6) as u64;
    let mut relax_cnt = 500; //u64 = two.pow() as u64;
                            /* Unexpectedly, relax_cnt = 500 gives 3% congestion, whereas relax_cnt = 50 gives 0.61%
                               The reason is, for relax_cnt = 50, there is a high read underflow
                               hence, the effective relax count becomes quite less
                            */

    oram_exp(
        two.pow(11), //11 working//15 means 2^15*4KB blocks = 2^15*2^12 = 2^27 = 128MB
        6,
        1,
        (burst_cnt),     /* Only access few elements at the beginnig */
        (relax_cnt),     /* Then perform nothing for rest of the time */
        total_sim_steps, //total_sim_steps/_N should be 2^11?
    );
}
