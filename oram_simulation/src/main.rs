use tfhe::boolean::backward_compatibility::client_key;
use tfhe::integer::bigint::U1024;
use tfhe::prelude::*;
use tfhe::{generate_keys, set_server_key, ConfigBuilder, FheInt32, FheUint1024, FheBool, FheUint, FheUint1024Id};
extern crate chrono;
use chrono::Local;
use rand::distributions::{Distribution, Uniform};
use rand::rngs::ThreadRng;
use rand::Rng;
use std::collections::VecDeque;
use std::collections::HashMap;
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
        2//Temporarily it is changed to 2
    };
}

static mut N: u32 = 8;
static mut L: u32 = 4;
static mut R: u32 = 1;
static mut C: u32 = 1; /* Initial number of replicas */
static mut Z: u32 = 1;
static mut B: u32 = 4096; /* Common block size is: 4KB
But RLWE can encrypt 3KB per ciphertext. 
So, block size must be set to multiple of 3KB.
Moreover, some place must be kept reserved for storing metadata */
static mut epoch: u32 = 14; //2(N-1)
static mut rate_ratio: u32 = 10; //Ratio of server's processing : Client's processing
static mut two: u32 = 2;
static mut idx: usize = 0;
static mut tu: u64 = 0; /* Count of time unit */
static mut read_failure_cnt: u64 = 0; /* The number of times the read operation failed */
static mut write_failure_cnt: u64 = 0; /* The number of times the write operation failed */
static mut bg_failure_cnt: u64 = 0; /* The number of times the background operation caused buffer overflow */
static mut max_burst_cnt: u64 = 0; /* The number of blocks the client retrives in a burst */
static mut min_relax_cnt: u64 = 0; /* The amount of time (in terms of step processing), the client relaxes after each burst */


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
            m: m {
                id: 0,
                lf: 0,
            },
            d: Vec::new(),
        }
    }

    /* Fill all NUMu64! with same data */
    fn fillData(&mut self, d:FheUint1024){
        for _ in 0..NUMu64!(){
            self.d.push(d.clone());
        }
    }

    /* Print data */
    fn printData(&mut self, client_key:&ClientKey){
        for _ in 0..NUMu64!(){
            //self.d.push(d.clone());
        }
    }
}

impl Bucket {
    // Method to create a new Bucket
    fn new(label: u32) -> Self {
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
            blocks: Vec::new(),
        }
    }

    // Method to add a u32 to the end of the list
    fn insert(&mut self, value: u32) {
        self.blocks.push(value);
    }

    // Method to remove an item by its value
    fn remove(&mut self, value: u32) -> u32 {
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

        let mut current: u32 = self.blocks.len() as u32;
        total += current as u64;
        sq_total += current.pow(2) as u64;

        self.stat.avg = (total as f64 / self.stat.access_cnt as f64) as f64;

        self.stat.sq_avg = (sq_total as f64 / self.stat.access_cnt as f64) as f64;

        /* var(X) = E[x^2] - E[x]^2*/
        self.stat.var = self.stat.sq_avg - (self.stat.avg * self.stat.avg);

        if current > self.stat.max {
            self.stat.max = current;
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
            var: self.stat.var,    //Variance of occupancy
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
            self.stat.sty_cnt
            //self.blocks,
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
            var: self.stat.var,    //Variance of occupancy
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

        AvailabilityTS(Tcur, x, w);

        x = rng.gen_range(two.pow(L - 1)..(two.pow(L) - 1));
        w = rng.gen_range(1..(two.pow(L - R) - 1));

        //block.m = M;
        //block.d = [5,5];

        //tfhe_exp();

        AvailabilityTS(Tcur, x, w);
        oram_exp();
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
unsafe fn oram_exp() {
    /* Set experimentation parameters fist */
    N = two.pow(20);//1GB database
    R = 1;
    Z = 6;//Number of slots in a bucket
    C = Z/2;
    rate_ratio = 10;
    max_burst_cnt = 10*1024;//Assume each block is of 1KB and each burst is of 10MB
    min_relax_cnt = 5*60*1000;//Assume it is 5 minutes and 100 edges (i.e., 2Z*1000*1KB = 12MB/s) are processed each second

    /* Derived parameters */
    L = ((N as f64).log2() as u32) + 1;
    epoch = 2 * (N - 1);

    /* Local variable */
    let mut edge: u32; /* Determines which edge to process now */
    let ITR_CNT: u64 = 500000; /* The experiment will run until t reaches itr_cnt */
    let mut node_que: VecDeque<u32> = VecDeque::new(); /* Queue of parent nodes */
    let mut b: u32; /* Holds the label of the current bucket */
    let mut p: usize; /* Holds the label of the parent node of the current edge */
    let mut x: u32;
    let mut tree: Vec<Bucket> = Vec::with_capacity(2 * (N as usize) - 1);
    let mut fetched_blk_cnt = 0;
    let mut relax_cnt = 0;

    printdbgln!(
        1,
        "Value of N = {}, R = {}, L = {}, Z = {}, epoch = {}, rate_ratio = {}",
        N,
        R,
        L,
        Z,
        epoch,
        rate_ratio
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
    edge = 1; /* Initialize with edge count 1 */

    /* Do the experiment until a specified time */
    while tu < ITR_CNT {
        if (fetched_blk_cnt < max_burst_cnt) {
            if (tu % (rate_ratio as u64)) == 0 {
                let mut read_success: bool;
                /* Perform one read */
                read_success = oram_read(&mut randomness, &mut r_dist, &mut tree);
    
                /* Perform one write */
                if (read_success == true){
                    oram_write(&mut randomness, &mut x_dist, &mut w_dist, &mut tree);
                }
            }
            
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

            bg_process(&mut tree, p, 2 * p);
            tu += 1;

            bg_process(&mut tree, p, 2 * p + 1);
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

    //experimental_function();
}

unsafe fn oram_write(
    mut randomness: &mut ThreadRng,
    mut x_dist: &mut Uniform<u32>,
    mut w_dist: &mut Uniform<u32>,
    tree: &mut Vec<Bucket>,
) {
    //Randomly select a new leaf node and write node
    let x = randomness.sample(*x_dist);
    let w = randomness.sample(*w_dist);

    if (tree[w as usize - 1].blocks.len() < Z as usize) {
        //Bucket with label w is stored in location (w-1)
        //Write a block having leaf label x, into the bucket(w)
        tree[w as usize - 1].insert(x);
        tree[w as usize - 1].calc_stat(); //Update statistics
    } else {
        write_failure_cnt += 1;
    }

    tree[w as usize - 1].stat.w_cnt += 1;
    tree[x as usize - 1].stat.x_cnt += 1;

}

unsafe fn oram_read(
    mut randomness: &mut ThreadRng,
    mut r_dist: &mut Uniform<u32>,
    tree: &mut Vec<Bucket>,
) -> bool {
    let mut success: bool = true;

    //For experiment, randomly select a leaf node to read
    let r = randomness.sample(*r_dist);

    //Bucket with label r is stored in location (r-1)
    //For experimentation purpose always read the first item from the bucket
    //So, only using the bare remove() method of list data-type
    if (tree[r as usize - 1].blocks.len() > 0) {
        tree[r as usize - 1].blocks.remove(0);
        tree[r as usize - 1].calc_stat(); //Update statistics
    } else {
        read_failure_cnt += 1;//In real scenario, this will not happen unless the server misbehaves. Because, the client will not issue read in that case.
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
        while j < ML.len(){
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
        while j < MU.len(){
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
        while j < ML.len(){
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

    for b in 1..=(two.pow(L) - 1) {
        tree[b as usize - 1].print_stat();
    }

    printdbgln!(1, "Read failure count: {}, write failure count: {}, background failure count: {}", read_failure_cnt, write_failure_cnt, bg_failure_cnt);
}

/* Inspired from the movement algorithm in sumit_draft.docx */
unsafe fn bg_process(tree: &mut Vec<Bucket>, upper: u32, lower: u32) {
    let mut l_upper: u32 = ((upper as f64).log2() as u32) + 1;
    let mut l_lower: u32 = l_upper + 1;
    let mut blk_num: u32;
    let mut org_lower_buk_sz: usize;
    let mut change_flag: bool = false;

    /* First move down */
    for i in (0..tree[upper as usize - 1].blocks.len()).rev() {
        //Iterate in reverse order to avoid shifting of indices due to removal
        /* First move down, but before that store the original size of the lower bucket */
        org_lower_buk_sz = tree[lower as usize - 1].blocks.len();
        if (lower == (tree[upper as usize - 1].blocks[i] >> (L - l_lower))) {
            blk_num = tree[upper as usize - 1].blocks.remove(i); /* Remove the block from the upper bucket */
            tree[lower as usize - 1].insert(blk_num); /* Insert at the end of the lower bucket */
            change_flag = true;

            if ((lower % 2) == 0 ){ //Even means, moving to the left child
                tree[upper as usize - 1].stat.out_lft_cnt += 1;
                tree[lower as usize - 1].stat.in_up_cnt += 1;
            } else {
                tree[upper as usize - 1].stat.out_rgt_cnt += 1;
                tree[lower as usize - 1].stat.in_up_cnt += 1;
            }
        } else {
            tree[upper as usize - 1].stat.sty_cnt += 1;
        }
    }

    /* Do not count the failure, when moving to the leaf bucket.
       Already there are some problems regarding the lower buckets, as it is going beyond 24.
     */
    if (tree[lower as usize - 1].blocks.len() > Z as usize) && (l_lower < L) {
        bg_failure_cnt += 1;
    }

    /* Then move up, but before that store the original size of the lower bucket */
    org_lower_buk_sz = tree[lower as usize - 1].blocks.len();

    /* Only perform movement of the items which were originally present in the lower bucket */
    for i in (0..org_lower_buk_sz).rev() {
        //Iterate in reverse order to avoid shifting of indices due to removal
        if (lower != (tree[lower as usize - 1].blocks[i] >> (L - l_lower))) {
            blk_num = tree[lower as usize - 1].blocks.remove(i); /* Remove the block from the lower bucket */
            tree[upper as usize - 1].insert(blk_num); /* Insert at the end of the upper bucket */
            change_flag = true;
            if ((lower % 2) == 0 ){ //Even means, moving to the left child
                tree[upper as usize - 1].stat.in_lft_cnt += 1;
                tree[lower as usize - 1].stat.out_up_cnt += 1;
            }else{
                tree[upper as usize - 1].stat.in_rgt_cnt += 1;
                tree[lower as usize - 1].stat.out_up_cnt += 1;
            }
        } else {
            tree[lower as usize - 1].stat.sty_cnt += 1;
        }
    }

    if (tree[upper as usize - 1].blocks.len() > Z as usize) {
        bg_failure_cnt += 1;
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

unsafe fn experimental_function() {
    // Basic configuration to use homomorphic integers
    let config = ConfigBuilder::default().build();
 
    // Key generation
    let (client_key, server_keys) = generate_keys(config);
    
    let mut clear_a = 0x1;
    let mut clear_b = 0x2;

    //Create block A
    let mut blkA = blk::new(0, 0);
    blkA.fillData(FheUint1024::encrypt(0_u64, &client_key));

    //Create block B
    let mut blkB = blk::new(1, 0);
    blkB.fillData(FheUint1024::encrypt(1_u64, &client_key));

    // Encrypting the input data using the (private) client_key
    // FheInt32: Encrypted equivalent to i32
    let mut encrypted_a = FheInt32::encrypt(clear_a, &client_key);
    let mut encrypted_b = FheInt32::encrypt(clear_b, &client_key);
    let encBit = FheBool::encrypt(true, &client_key);
    printdbgln!(1, "Line: {}", line!());
    
    // On the server side:
    set_server_key(server_keys);
    printdbgln!(1, "Line: {}", line!());
 
    /*
    let mut encrypted_tmp = encrypted_a.clone();

    encrypted_a = encBit.select(&encrypted_b, &encrypted_a);

    encrypted_b = encBit.select(&encrypted_tmp, &encrypted_b);
    
    let clear_a: i32 = encrypted_a.decrypt(&client_key);
    let clear_b: i32 = encrypted_b.decrypt(&client_key);
    */
    cswap_blk(&encBit, &mut blkA, &mut blkB);
    //cswap_blk(&encBit, &mut encrypted_a, &mut encrypted_b);

    printdbgln!(1, "Line: {}", line!());

    clear_a = encrypted_a.decrypt(&client_key);
    clear_b = encrypted_b.decrypt(&client_key);
 
    printdbgln!(1, "After swapping the values are: a={} and b={}", clear_a, clear_b);
 
 }

 unsafe fn cswap_blk(encBit:&FheBool, blkA:&mut blk, blkB:&mut blk) {
    //let mut encTmp = blkA.clone();

    for i in 0..NUMu64!(){
        blkA.d[i] = encBit.select(&blkB.d[i], &blkA.d[i]);
        //*blkB = encBit.select(&encTmp, &blkB);
        //*blkB = encBit.select(&encTmp, &blkB);   
    }
 }