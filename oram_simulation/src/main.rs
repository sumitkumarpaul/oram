use tfhe::prelude::*;
use tfhe::{generate_keys, set_server_key, ConfigBuilder, FheInt32, FheBool};
extern crate chrono;
use chrono::Local;
use rand::distributions::{Distribution, Uniform};
use rand::rngs::ThreadRng;
use rand::Rng;
use std::collections::VecDeque;
use std::collections::HashMap;
use std::mem::MaybeUninit;
use tfhe::prelude::*;

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

static mut N: u32 = 8;
static mut L: u32 = 4;
static mut R: u32 = 1;
static mut C: u32 = 1; /* Initial number of replicas */
static mut Z: u32 = 1;
static mut epoch: u32 = 14; //2(N-1)
static mut rate_ratio: u32 = 10; //Ratio of server's processing : Client's processing
static mut two: u32 = 2;
static mut idx: usize = 0;
static mut tu: u64 = 0; /* Count of time unit */


struct m {
    id: u32,
    lf: u32,
}
struct blk {
    m: m,
    d: [u32; 2],
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
    max: u32,
    avg: f64,
    var: f64,    //Variance of occupancy
    sq_avg: f64, //Average of the square of the occupancy, required for calculating the variance
}

impl Bucket {
    // Method to create a new Bucket
    fn new(label: u32) -> Self {
        Bucket {
            b: label,
            stat: Stat {
                access_cnt: 0,
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
    {:.2}\t\
    {:.2}\t\
    {}",
            self.b,
            self.stat.access_cnt,
            self.stat.avg,
            self.stat.var,
            self.stat.max,
            //self.blocks,
        );

        Stat {
            access_cnt: self.stat.access_cnt,
            max: self.stat.max,
            avg: self.stat.avg,
            var: self.stat.var,    //Variance of occupancy
            sq_avg: self.stat.sq_avg, //Average of the square of the occupancy, required for calculating the variance
        }
    }
}


fn main() {

    unsafe {
        //oram_exp();
        //BG();
        experimental_function();
    }
}

unsafe fn oram_exp() {
    /* Set experimentation parameters fist */
    N = two.pow(3);
    R = 1;
    Z = 6;//Number of slots in a bucket
    C = Z/2;

    /* Derived parameters */
    L = ((N as f64).log2() as u32) + 1;
    epoch = 2 * (N - 1);

    /* Local variable */
    let mut tree: Vec<Bucket> = Vec::with_capacity(2 * (N as usize) - 1);

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

unsafe fn experimental_function() {
    // Basic configuration to use homomorphic integers
    let config = ConfigBuilder::default().build();
 
    // Key generation
    let (client_key, server_keys) = generate_keys(config);
    
    let clear_a = 32i32;
    let clear_b = -45i32;
    
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
    cswap_blk(&encBit, &mut encrypted_a, &mut encrypted_b);

    printdbgln!(1, "Line: {}", line!());
 
    printdbgln!(1, "After swapping the values are: a={} and b={}", clear_a, clear_b);
 
 }

 unsafe fn cswap_blk(encBit:&FheBool, encA:&mut FheInt32, encB:&mut FheInt32) {
    let mut encTmp = encA.clone();

    *encA = encBit.select(&encA, &encB);

    *encB = encBit.select(&encA, &encB);
 }