use tfhe::boolean::backward_compatibility::client_key;
use tfhe::integer::bigint::U1024;
use tfhe::prelude::*;
use tfhe::{
    generate_keys, set_server_key, ConfigBuilder, FheBool, FheInt32, FheUint, FheUint1024,
    FheUint1024Id,
};
extern crate chrono;
use chrono::Local;
use rand::distributions::{Distribution, Uniform};
use rand::rngs::ThreadRng;
use rand::Rng;
use std::collections::HashMap;
use std::collections::VecDeque;
use std::mem::MaybeUninit;
use tfhe::prelude::*;
use tfhe::ClientKey;

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
static mut Z: u32 = 6;
static mut B: u32 = 4096; /* Common block size is: 4KB
                          But RLWE can encrypt 3KB per ciphertext.
                          So, block size must be set to multiple of 3KB.
                          Moreover, some place must be kept reserved for storing metadata */
static mut epoch: u32 = 14; //2(N-1)
static mut rate_ratio: u32 = 10; //Ratio of server's processing : Client's processing
static mut two: u32 = 2;
static mut idx: usize = 0;
static mut tu: u64 = 0; /* Count of time unit */
static mut read_underflow_cnt: u64 = 0; /* The number of times the read operation failed */
static mut write_failure_cnt: u64 = 0; /* The number of times the write operation failed */
static mut routing_congestion_cnt: u64 = 0; /* The number of times the background operation caused buffer overflow */
static mut max_burst_cnt: u64 = 0; /* The number of blocks the client retrives in a burst */
static mut min_relax_cnt: u64 = 0; /* The amount of time (in terms of step processing), the client relaxes after each burst */
static mut global_max_bucket_load: u32 = 0; /* Maximum load occurred in any bucket */
static mut total_num_removed: u64 = 0;/* Total number of blocks removed from its leaf location */
static mut total_num_placed: u64 = 0;/* How many number of blocks are returned to place by the routing process */
static mut last_placement_tu: u64 = 0;/* When the last block is placed to its destined leaf */

struct m {
    id: u32,
    lf: u32,
}
struct blk {
    m: m,
    d: Vec<FheUint<FheUint1024Id>>,
}

#[derive(Debug)]
struct Bucket {
    b: u32,           //The label of this bucket
    blocks: Vec<u32>, //List holding the leaf identifiers of the blocks
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

impl blk {
    // Method to create a new Bucket
    fn new(id: u32, lf: u32) -> Self {
        blk {
            m: m { id: 0, lf: 0 },
            d: Vec::new(),
        }
    }

    /* Fill all NUMu64! with same data */
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
            blocks: vec![0; Z as usize],
        }
    }

    // Method to add a u32(which contains the metadata m.x) in the place of 0
    unsafe fn insert(&mut self, value: u32) -> bool {
        let mut success:bool = false;

        if self.occupancy() < Z as usize {
            if let Some(pos) = self.blocks.iter().position(|&x| x == 0) {
                self.blocks[pos] = value;
                success = true;
            }
        }

        return  success;
    }

    // Number of non empty slots
    fn occupancy(&mut self) -> usize {
        let mut occuCnt: usize = 0;

        unsafe {
            for i in 0..Z {
                if self.blocks[i as usize] != 0 {
                    occuCnt += 1;
                }
            }   
        }

        return occuCnt;
    }
    
    // Method to remove an item from the stated index and insert 0 in that place
    fn remove(&mut self, index: usize) -> u32 {
        let mut removed_item: u32 = 0;

        removed_item = self.blocks[index];
        self.blocks[index] = 0;

        return removed_item;
    }
    
    // Method to remove an item by its value
    fn removeVal(&mut self, value: u32) -> u32 {
        let mut removed_item: u32 = 0;

        if let Some(pos) = self.blocks.iter().position(|&x| x == value) {
            removed_item = self.blocks[pos];
            self.blocks.remove(pos);
        }

        return removed_item;
    }
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
    fn print_stat(&mut self) -> Stat {
        printdbgln!(
            1,
            "Bucket[{}]:\t\
    {}\t\
    {}\t\
    {}\t\
    {}\t\
    {:.2}\t\
    {:.2}\t\
    {}\t\
    {}\t\
    {}\t\
    {}\t\
    {}\t\
    {}\t\
    {}\t\
    {}",
            self.b,
            self.stat.access_cnt,
            self.stat.r_cnt,
            self.stat.w_cnt,
            self.stat.x_cnt,
            self.stat.avg,
            self.stat.var,
            self.stat.max,
            self.stat.out_up_cnt,
            self.stat.out_lft_cnt,
            self.stat.out_rgt_cnt,
            self.stat.in_up_cnt,
            self.stat.in_lft_cnt,
            self.stat.in_rgt_cnt,
            self.stat.sty_cnt //self.blocks,
        );

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
    let mut M = m { id: 5, lf: 5 };

    //let mut block = blk { m: M, d: [5, 5] };

    let mut Tcur: u32;
    let mut x: u32;
    let mut w: u32;

    unsafe {
        Tcur = 0;
        let mut rng = rand::thread_rng();
        x = rng.gen_range(two.pow(L - 1)..(two.pow(L) - 1));
        w = rng.gen_range(1..(two.pow(L - R) - 1));

        //AvailabilityTS(Tcur, x, w);

        x = rng.gen_range(two.pow(L - 1)..(two.pow(L) - 1));
        w = rng.gen_range(1..(two.pow(L - R) - 1));

        //block.m = M;
        //block.d = [5,5];

        //tfhe_exp();

        //AvailabilityTS(Tcur, x, w);
        
        //Comment out some experiments
        if false {
        /* Experiment 1 */
        oram_exp(two.pow(26), /* Kept block size 4KB as per other ORAM paper
                                         256GB remote storage.
                                         2^26*4KB blocks. With compute canada resource cannot simulate larger remote storage
                                      */
        6, /* Number of slots. Kept is same as PathORAM */
        1, /* Client and server has same processing speed. Worst case scenario.
                           in general, the server is much faster */
        (1024*256), /* 1GB=1024*256 4KB blocks */
        (60*60*1), /* Client will relax for 60 minutes. In the meantime, the server will keep routing.
                                     Assumed, the server processes one edge per second.
                                     i.e., 2Z blocks each having 4KB
                                     Which turns out to be server processes: 2*6*4KB = 48KB/s */
        two.pow(20) as u64);/* Experiment runs for 2^29 steps.
                                             i.e., in this case more than server capacity number of blocks are accessed */

        /* Experiment 2 */
        oram_exp(two.pow(26), /* Kept block size 4KB as per other ORAM paper
                                         256GB remote storage.
                                         2^26*4KB blocks. With compute canada resource cannot simulate larger remote storage
                                      */
        6, /* Number of slots. Kept is same as PathORAM */
        1, /* Client and server has same processing speed. Worst case scenario.
                           in general, the server is much faster */
        (12*256), /* 12MB=12*256 4KB blocks */
        (5*60*1), /* Client will relax for 5 minutes. In the meantime, the server will keep routing.
                                     Assumed, the server processes one edge per second.
                                     i.e., 2Z blocks each having 4KB
                                     Which turns out to be server processes: 2*6*4KB = 48KB/s */
        two.pow(20) as u64);/* Experiment runs for 2^29 steps.
                                             i.e., in this case more than server capacity number of blocks are accessed */


        /* Experiment 3 */
        oram_exp(two.pow(26), /* Kept block size 4KB as per other ORAM paper
                                         256GB remote storage.
                                         2^26*4KB blocks. With compute canada resource cannot simulate larger remote storage
                                      */
        6, /* Number of slots. Kept is same as PathORAM */
        1, /* Client and server has same processing speed. Worst case scenario.
                           in general, the server is much faster */
        (12*256), /* 12MB=12*256 4KB blocks */
        (5*60*1), /* Client will relax for 5 minutes. In the meantime, the server will keep routing.
                                     Assumed, the server processes one edge per second.
                                     i.e., 2Z blocks each having 4KB
                                     Which turns out to be server processes: 2*6*4KB = 48KB/s */
        two.pow(29) as u64);/* Experiment runs for 2^29 steps.
                                             i.e., in this case more than server capacity number of blocks are accessed */

        /* Experiment 4 */
        oram_exp(two.pow(26), /* Kept block size 4KB as per other ORAM paper
                                         256GB remote storage.
                                         2^26*4KB blocks. With compute canada resource cannot simulate larger remote storage
                                      */
        6, /* Number of slots. Kept is same as PathORAM */
        1, /* Client and server has same processing speed. Worst case scenario.
                           in general, the server is much faster */
        (10240*256), /* 10GB=10240*256 4KB blocks */
        (two.pow(29) as u64 - (5*60*1)as u64) as u64, /* After fetching 10GB data, the client will not access anymore */
        two.pow(29) as u64);/* Experiment runs for 2^29 steps.
                                             i.e., in this case more than server capacity number of blocks are accessed */
        }
        experimental_function();
    }
    
}

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
unsafe fn oram_exp(_N: u32, _Z: u32, _rate_ratio: u32, _max_burst_cnt: u64, _min_relax_cnt: u64, _ITR_CNT: u64) {
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
    let ITR_CNT: u64 = _ITR_CNT; /* The experiment will run until t reaches itr_cnt */
    let mut node_que: VecDeque<u32> = VecDeque::new(); /* Queue of parent nodes */
    let mut b: u32; /* Holds the label of the current bucket */
    let mut p: usize; /* Holds the label of the parent node of the current edge */
    let mut x: u32;
    let mut tree: Vec<Bucket> = Vec::with_capacity(2 * (N as usize) - 1);
    let mut fetched_blk_cnt = 0;
    let mut relax_cnt = 0;

    printdbgln!(
        1,
        "Experimentation started at: {} with parameters: N = {}, Z = {}, rate_ratio = {}, max_burst_cnt = {}, min_relax_cnt = {}, ITR_CNT = {}",
        Local::now().format("%Y-%m-%d %H:%M:%S.%6f").to_string(),
        N,
        Z,
        rate_ratio,
        max_burst_cnt,
        min_relax_cnt,
        ITR_CNT
    );

    /* Loop from 1 to 2N - 1 */
    for i in 1..=(2 * (N as usize) - 1) {
        tree.push(Bucket::new(i as u32));
    }

    /* Initialize the ORAM with dummy data */
    oram_init(&mut tree);

    //Initialize the randomness
    let mut rng_x = rand::thread_rng();
    let mut rng_r = rand::thread_rng();
    let mut rng_w = rand::thread_rng();
    let mut randomness = rand::thread_rng();
    let mut r_dist = Uniform::new_inclusive(two.pow(L - 1), (two.pow(L) - 1));
    let mut x_dist = Uniform::new_inclusive(two.pow(L - 1), (two.pow(L) - 1));
    let mut w_dist = Uniform::new_inclusive(1, (two.pow(L - 1) - 1));

    node_que.push_front(tree[0].b); /* At first push the root bucket. Located in tree[0], but has label = 1 */
    tu = 0; /* Initialize with time count 0 */

    /* Do the experiment until a specified time */
    while tu < ITR_CNT {
        if (fetched_blk_cnt < max_burst_cnt) {
            //As each iteration, two edges are processed to make the rate same, two blocks are accessed as well

            //if (tu % (rate_ratio as u64)) == 0 {
            let mut read_success: bool;
            /* Perform one read */
            read_success = oram_remove(&mut randomness, &mut r_dist, &mut tree);

            /* Perform one write */
            if (read_success == true) {
                oram_insert(&mut randomness, &mut x_dist, &mut w_dist, &mut tree);
            }

            /* Perform second read */
            read_success = oram_remove(&mut randomness, &mut r_dist, &mut tree);

            /* Perform second write */
            if (read_success == true) {
                oram_insert(&mut randomness, &mut x_dist, &mut w_dist, &mut tree);
            }
            //}

            fetched_blk_cnt += 1;
        } else {
            if (relax_cnt < min_relax_cnt) {
                relax_cnt += 1;
            } else {
                fetched_blk_cnt = 0;
                relax_cnt = 0;
            }
        }

        /* During each step, two different edges are processed */
        if let Some(p) = node_que.pop_back() {
            node_que.push_front(2 * p); //Actually 2p bucket. -1 becasue of 0 index
            node_que.push_front(2 * p + 1); //2p+1

            let (mut muUp, mut muDn) = calcMovement(&mut tree, p, 2 * p);

            permute(&mut tree, p, 2 * p, &mut muUp, &mut muDn);
            tu += 1;

            (muUp, muDn) = calcMovement(&mut tree, p, 2 * p + 1);

            permute(&mut tree, p, 2 * p + 1, &mut muUp, &mut muDn);
            tu += 1;
        } else {
            printdbgln!(0, "Queue is empty");
        }

        /* Re-initialize the queue */
        if (tu % (epoch as u64)) == 0 {
            node_que.clear();
            node_que.push_front(tree[0].b);
            //printdbgln!(0,  "Clearning queue");
        }
    }

    oram_stat_print(&mut tree);

    printdbgln!(1, "Experimentation ended at: {}", Local::now().format("%Y-%m-%d %H:%M:%S.%6f").to_string());

    //experimental_function();
}

unsafe fn oram_insert(
    mut randomness: &mut ThreadRng,
    mut x_dist: &mut Uniform<u32>,
    mut w_dist: &mut Uniform<u32>,
    tree: &mut Vec<Bucket>,
) {
    //Randomly select a new leaf node and write node
    let x = randomness.sample(*x_dist);
    let w = randomness.sample(*w_dist);

    if (tree[w as usize - 1].occupancy() < Z as usize) {
        //Bucket with label w is stored in location (w-1)
        //Write a block having leaf label x, into the bucket(w)
        tree[w as usize - 1].insert(x);
        tree[w as usize - 1].calc_stat(); //Update statistics
    } else {
        /* Cannot write to the block, as it is already full */
        write_failure_cnt += 1;
    }

    tree[w as usize - 1].stat.w_cnt += 1;
    tree[x as usize - 1].stat.x_cnt += 1;
}

unsafe fn oram_remove(
    mut randomness: &mut ThreadRng,
    mut r_dist: &mut Uniform<u32>,
    tree: &mut Vec<Bucket>,
) -> bool {
    let mut success: bool = true;

    //For experiment, randomly select a leaf node to read
    let r = randomness.sample(*r_dist);
    total_num_removed += 1;

    //Bucket with label r is stored in location (r-1)
    //For experimentation purpose always read the first item from the bucket
    //So, only using the bare remove() method of list data-type
    if (tree[r as usize - 1].occupancy() > 0) {
        tree[r as usize - 1].remove(0);
        tree[r as usize - 1].calc_stat(); //Update statistics
    } else {
        read_underflow_cnt += 1; //In real scenario, this will not happen unless the server misbehaves. Because, the client will not issue read in that case.
        success = false;
    }
    tree[r as usize - 1].stat.r_cnt += 1;
    //printdbgln!(1, "After reading, length of bucket[{}]:{}", r, tree[r as usize - 1].blocks.len());

    return success;
}

unsafe fn oram_init(tree: &mut Vec<Bucket>) {
    //For experiment, randomly select a leaf node to read
    for l in two.pow(L - 1)..=(two.pow(L) - 1) {
        /* Insert C number of replicas, in each replica the same address is specified */
        for i in 0..C {
            tree[l as usize - 1].insert(l);
        }
        tree[l as usize - 1].calc_stat();
    }
}

/*
fn move_U2L(MU: &mut [i32], ML: &mut [i32]) {
    let mut i = 0;
    let mut j = 0;

    printdbgln!(1, "======================");
    printdbgln!(1, "Moving upper to lower:");
    printdbgln!(1, "======================");

    printdbg!(1, "MU array before operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array before operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    while (i < MU.len() && j < ML.len()) {
        if MU[i] == 1 {
            while ((j < ML.len()) && (ML[j] != 2)) {
                j += 1;
            }

            if (j == ML.len()) {
                break;
            }
            printdbgln!(1, "Moving down from MU[{}] to ML[{}]", i, j);

            MU[i] = 0;
            ML[j] = 0;
            j += 1;
        }

        i += 1;
    }

    // Using a for loop to iterate through the array
    printdbg!(1, "MU array after operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array after operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");
}
*/

fn move_U2L_Obliviously(MU: &mut [i32], ML: &mut [i32]) {
    let mut i = 0;
    let mut j = 0;

    printdbgln!(1, "===================================");
    printdbgln!(1, "Moving upper to lower obliviously: ");
    printdbgln!(1, "===================================");

    printdbg!(1, "MU array before operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array before operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    while i < MU.len() {
        j = 0;
        while j < ML.len() {
            /* Upper block is required to move to lower layer and lower layer is empty */
            if (MU[i] == 1) && (ML[j] == 2) {
                printdbgln!(1, "Moving down from MU[{}] to ML[{}]", i, j);
                /* After movement, the upper layer becomes empty and lower layer becomes staty */
                MU[i] = 2;
                ML[j] = 0;
            } else {
                /* Keep the elements same */
                MU[i] = MU[i];
                ML[j] = ML[j];
            }
            j += 1;
        }

        i += 1;
    }

    // Using a for loop to iterate through the array
    printdbg!(1, "MU array after operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array after operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");
}

fn move_L2U_Obliviously(MU: &mut [i32], ML: &mut [i32]) {
    let mut i = 0;
    let mut j = 0;

    printdbgln!(1, "==================================");
    printdbgln!(1, "Moving lower to upper obliviously:");
    printdbgln!(1, "==================================");

    printdbg!(1, "MU array before operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array before operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    while i < ML.len() {
        j = 0;
        while j < MU.len() {
            /* Lower block is required to move to upper layer and upper layer is empty */
            if (ML[i] == 1) && (MU[j] == 2) {
                printdbgln!(1, "Moving down from ML[{}] to MU[{}]", i, j);
                /* After movement, the lower layer becomes empty and upper layer becomes stay */
                ML[i] = 2;
                MU[j] = 0;
            } else {
                /* Keep the elements same */
                ML[i] = ML[i];
                MU[j] = MU[j];
            }
            j += 1;
        }

        i += 1;
    }

    // Using a for loop to iterate through the array
    printdbg!(1, "MU array after operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array after operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");
}

/*
fn move_L2U(MU: &mut [i32], ML: &mut [i32]) {
    let mut i = 0;
    let mut j = 0;

    printdbgln!(1, "======================");
    printdbgln!(1, "Moving lower to upper:");
    printdbgln!(1, "======================");


    printdbg!(1, "MU array before operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array before operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    while (i < ML.len() && j < MU.len()) {
        if ML[i] == 1 {
            while ((j < MU.len()) && (MU[j] != 2)) {
                j += 1;
            }

            if (j == MU.len()) {
                break;
            }
            printdbgln!(1, "Moving up from ML[{}] to MU[{}]", i, j);

            MU[j] = 0;
            ML[i] = 0;

            j += 1;
        }

        i += 1;
    }

    // Using a for loop to iterate through the array
    printdbg!(1, "MU array after operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array after operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");
}
*/

fn process_swap(MU: &mut [i32], ML: &mut [i32]) {
    let mut i = 0;
    let mut j = 0;

    printdbgln!(1, "====================");
    printdbgln!(1, "Performing swapping:");
    printdbgln!(1, "====================");

    printdbg!(1, "MU array before operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array before operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    while (i < MU.len() && j < ML.len()) {
        if MU[i] == 1 {
            while ((j < ML.len()) && (ML[j] != 1)) {
                j += 1;
            }

            if (j == ML.len()) {
                break;
            }
            printdbgln!(1, "Swap between MU[{}] and ML[{}]", i, j);

            MU[i] = 0;
            ML[j] = 0;

            j += 1;
        }

        i += 1;
    }

    // Using a for loop to iterate through the array
    printdbg!(1, "MU array after operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array after operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");
}

fn process_swap_Obliviously(MU: &mut [i32], ML: &mut [i32]) {
    let mut i = 0;
    let mut j = 0;

    printdbgln!(1, "================================");
    printdbgln!(1, "Performing swapping obliviously:");
    printdbgln!(1, "================================");

    printdbg!(1, "MU array before operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array before operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    while i < MU.len() {
        j = 0;
        while j < ML.len() {
            /* Upper block is required to move to lower layer and lower layer is required to move upper layer */
            if (MU[i] == 1) && (ML[j] == 1) {
                printdbgln!(1, "Swapping between MU[{}] to ML[{}]", i, j);
                /* After movement, both the upper and lower slots become stable */
                MU[i] = 0;
                ML[j] = 0;
            } else {
                /* Keep the elements same */
                MU[i] = MU[i];
                ML[j] = ML[j];
            }
            j += 1;
        }

        i += 1;
    }

    // Using a for loop to iterate through the array
    printdbg!(1, "MU array after operation: ");
    for element in MU.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");

    printdbg!(1, "ML array after operation: ");
    for element in ML.iter() {
        printdbg!(1, "{}, ", element);
    }
    printdbgln!(1, "");
}

fn BG() {
    let mut MU = [1, 1, 1, 1, 1, 0, 0, 0, 0, 0]; // Movement of the upper bucket
    let mut ML = [0, 0, 2, 2, 2, 0, 0, 1, 0, 0]; // Movement of the lower bucket

    //let mut MU = [1,1,1,1,1,1,2,1,1,1]; // Movement of the upper bucket
    //let mut ML = [1,1,1,2,1,1,1,1,0,1]; // Movement of the lower bucket

    process_swap_Obliviously(&mut MU, &mut ML);
    move_U2L_Obliviously(&mut MU, &mut ML);
    move_L2U_Obliviously(&mut MU, &mut ML);
}

unsafe fn oram_stat_print(tree: &mut Vec<Bucket>) {
    printdbgln!(1, "Bucket\t\ta_cnt\tr_cnt\tw_cnt\tx_cnt\tavg\tvar\tmax\tout_up\tout_lft\tout_rgt\tin_up\tin_lft\tin_rgt\tsty");

    /*
    for b in 1..=(two.pow(L) - 1) {
        tree[b as usize - 1].print_stat();
    }*/

    /* Note: We are not calculating read error. i.e., the block must be availabel at some leaf but is not.
     Basically, if the server is honest(but curious) then that value must be zero, if routing_congestion_cnt = 0
    */

    printdbgln!(1, "Read underflow count: {}, write failure count: {}, routing congestion count: {}, global max load: {}, total number of removals: {}, total number of placements: {}, last placement occurred at: {}", read_underflow_cnt, write_failure_cnt, routing_congestion_cnt, global_max_bucket_load, total_num_removed, total_num_placed, last_placement_tu);
}

/* Inspired from the movement algorithm in sumit_draft.docx not according to the paper */
unsafe fn permute_Old(tree: &mut Vec<Bucket>, upper: u32, lower: u32) {
    let mut l_upper: u32 = ((upper as f64).log2() as u32) + 1;
    let mut l_lower: u32 = l_upper + 1;
    let mut blk_num: u32;
    let mut org_lower_buk_sz: usize;
    let mut change_flag: bool = false;

    /* First move down */
    for i in (0..tree[upper as usize - 1].occupancy()).rev() {
        //Iterate in reverse order to avoid shifting of indices due to removal
        /* First move down, but before that store the original size of the lower bucket */
        org_lower_buk_sz = tree[lower as usize - 1].occupancy();
        if (lower == (tree[upper as usize - 1].blocks[i] >> (L - l_lower))) {
            blk_num = tree[upper as usize - 1].remove(i); /* Remove the block from the upper bucket */
            tree[lower as usize - 1].insert(blk_num); /* Insert at the end of the lower bucket */
            change_flag = true;

            if ((lower % 2) == 0) {
                //Even means, moving to the left child
                tree[upper as usize - 1].stat.out_lft_cnt += 1;
                tree[lower as usize - 1].stat.in_up_cnt += 1;
            } else {
                tree[upper as usize - 1].stat.out_rgt_cnt += 1;
                tree[lower as usize - 1].stat.in_up_cnt += 1;
            }

            /* Means routing process is able to return back one block to its destined bucket */
            if (l_lower == L) {
                total_num_placed += 1;
                last_placement_tu = tu;
            }
        } else {
            tree[upper as usize - 1].stat.sty_cnt += 1;
        }
    }

    /* Do not count the failure, when moving to the leaf bucket.
      Already there are some problems regarding the lower buckets, as it is going beyond 24.
    */
    //if (tree[lower as usize - 1].blocks.len() > Z as usize) && (l_lower < L) {
    if (tree[lower as usize - 1].occupancy() > Z as usize) {
        routing_congestion_cnt += 1;
    }

    /* Then move up, but before that store the original size of the lower bucket */
    org_lower_buk_sz = tree[lower as usize - 1].occupancy();

    /* Only perform movement of the items which were originally present in the lower bucket */
    for i in (0..org_lower_buk_sz).rev() {
        //Iterate in reverse order to avoid shifting of indices due to removal
        if (lower != (tree[lower as usize - 1].blocks[i] >> (L - l_lower))) {
            blk_num = tree[lower as usize - 1].remove(i); /* Remove the block from the lower bucket */
            tree[upper as usize - 1].insert(blk_num); /* Insert at the end of the upper bucket */
            change_flag = true;
            if ((lower % 2) == 0) {
                //Even means, moving to the left child
                tree[upper as usize - 1].stat.in_lft_cnt += 1;
                tree[lower as usize - 1].stat.out_up_cnt += 1;
            } else {
                tree[upper as usize - 1].stat.in_rgt_cnt += 1;
                tree[lower as usize - 1].stat.out_up_cnt += 1;
            }
        } else {
            tree[lower as usize - 1].stat.sty_cnt += 1;
        }
    }

    if (tree[upper as usize - 1].occupancy() > Z as usize) {
        routing_congestion_cnt += 1;
    }

    /* Calculate the stat, whenever the node is accessed. Irrespective of change or no change */
    tree[upper as usize - 1].calc_stat();
    tree[lower as usize - 1].calc_stat();

    /* Print statistics, only if there is a change */
    if change_flag {
        //tree[upper as usize-1].print_stat();
        //tree[lower as usize-1].print_stat();
    }
}

unsafe fn calcMovement(tree: &mut Vec<Bucket>, upper: u32, lower: u32) -> (Vec<i32>, Vec<i32>) {
    let mut l_upper: u32 = ((upper as f64).log2() as u32) + 1;
    let mut l_lower: u32 = l_upper + 1;
    let mut muUp = Vec::new();
    let mut muDn = Vec::new();

    /* First upper bucket */
    for i in 0..Z {
        if tree[upper as usize - 1].blocks[i as usize] == 0 {
            muUp.push(EMPTY!());
        } else {
            if (lower == (tree[upper as usize - 1].blocks[i as usize] >> (L - l_lower))) {
                muUp.push(MOVE!());
            } else {
                muUp.push(NOT_MOVE!());
            }
        }
    }

    /* Then check the lower bucket */
    for i in 0..Z {
        if tree[lower as usize - 1].blocks[i as usize] == 0 {
            muDn.push(EMPTY!());
        } else {
            if (lower == (tree[lower as usize - 1].blocks[i as usize] >> (L - l_lower))) {
                muDn.push(NOT_MOVE!());
            } else {
                muDn.push(MOVE!());
            }
        }
    }

    (muUp, muDn)
}

/* Inspired from the movement algorithm in sumit_draft.docx not according to the paper */
unsafe fn permute(tree: &mut Vec<Bucket>, upper: u32, lower: u32, muUp: &mut Vec<i32>, muDn: &mut Vec<i32>) {
    
    if false {
    /* First swap */
    for i in 0..Z as usize {
        for j in 0..Z as usize {
            if (muUp[i] == MOVE!()) && (muDn[j] == MOVE!()) {
                let tmp:u32 = tree[upper as usize - 1].blocks[i];
                tree[upper as usize - 1].blocks[i] = tree[lower as usize - 1].blocks[j];
                tree[lower as usize - 1].blocks[j] = tmp;
                muUp[i] = NOT_MOVE!();
                muDn[j] = NOT_MOVE!();
            }
        }    
    }
    
    /* Move up */
    for i in 0..Z as usize {
        for j in 0..Z as usize {
            if (muUp[j] == EMPTY!()) && (muDn[i] == MOVE!()) {
                tree[upper as usize - 1].blocks[j] = tree[lower as usize - 1].blocks[i];
                tree[lower as usize - 1].blocks[i] = 0;
                muUp[j] = NOT_MOVE!();
                muDn[i] = EMPTY!();
            }
        }    
    }
}

    /* Move down */
    for i in 0..Z as usize {
        for j in 0..Z as usize {
            if (muUp[i] == MOVE!()) && (muDn[j] == EMPTY!()) {
                tree[lower as usize - 1].blocks[j] = tree[upper as usize - 1].blocks[i];
                tree[upper as usize - 1].blocks[i] = 0;
                muUp[i] = EMPTY!();
                muDn[j] = NOT_MOVE!();
            }
        }    
    }    
}


unsafe fn experimental_function() {
    let mut tree: Vec<Bucket> = Vec::with_capacity(2 * (N as usize) - 1);
    /* Loop from 1 to 2N - 1 */
    for i in 1..=(2 * (N as usize) - 1) {
        tree.push(Bucket::new(i as u32));
    }

    /* Initialize the ORAM with dummy data */
    oram_init(&mut tree);

    let upper: u32 = 3;
    let lower: u32 = 7;

    tree[upper as usize - 1].insert(11);
    tree[upper as usize - 1].insert(13);
    tree[upper as usize - 1].insert(15);
    tree[upper as usize - 1].insert(14);
    tree[upper as usize - 1].insert(9);
    tree[upper as usize - 1].insert(12);

    tree[lower as usize - 1].insert(14);
    tree[lower as usize - 1].insert(12);
    tree[lower as usize - 1].insert(10);
    tree[lower as usize - 1].insert(15);


    let (mut muUp, mut muDn) = calcMovement(&mut tree, upper, lower);
    
    printdbgln!(1, "Bucket({}): {:?}", upper, tree[upper as usize - 1].blocks);
    printdbgln!(1, "Bucket({}): {:?}", lower, tree[lower as usize - 1].blocks);
    printdbgln!(1, "muUp: {:?}", muUp);
    printdbgln!(1, "muDn: {:?}", muDn);

    permute(&mut tree, upper, lower, &mut muUp, &mut muDn);
    
    printdbgln!(1, "Bucket({}): {:?}", upper, tree[upper as usize - 1].blocks);
    printdbgln!(1, "Bucket({}): {:?}", lower, tree[lower as usize - 1].blocks);
    printdbgln!(1, "muUp: {:?}", muUp);
    printdbgln!(1, "muDn: {:?}", muDn);

}

unsafe fn cswap_blk(encBit: &FheBool, blkA: &mut blk, blkB: &mut blk) {
    //let mut encTmp = blkA.clone();

    for i in 0..NUMu64!() {
        blkA.d[i] = encBit.select(&blkB.d[i], &blkA.d[i]);
        //*blkB = encBit.select(&encTmp, &blkB);
        //*blkB = encBit.select(&encTmp, &blkB);
    }
}
