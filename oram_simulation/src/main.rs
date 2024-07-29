use tfhe::prelude::*;
use tfhe::{generate_keys, set_server_key, ConfigBuilder, FheInt32};
extern crate chrono;
use chrono::Local;
use rand::distributions::{Distribution, Uniform};
use rand::rngs::ThreadRng;
use rand::Rng;
use std::collections::VecDeque;
use std::collections::HashMap;
use std::mem::MaybeUninit;

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

fn main() {

    unsafe {

        experimental_function();
    }
}

unsafe fn experimental_function() {
    let mut rng = rand::thread_rng();
    let range = Uniform::new_inclusive(8, 15);
    let mut list: Vec<u32> = Vec::new();

    for _ in 0..1000000 {
        list.push(rng.sample(range));
    }

    // Create a histogram (a HashMap to count occurrences)
    let mut histogram = HashMap::new();

    for &number in &list {
        let count = histogram.entry(number).or_insert(0);
        *count += 1;
    }

    // Print the histogram
    for (value, count) in &histogram {
        println!("{}: {}", value, count);
    }
}
