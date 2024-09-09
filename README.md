# ORAM-Simulator
We propose *RouterORAM*, which can hide a client's access pattern during remote storage access.
The key benefits of *RouterORAM* is $O(1)$-latency and $O(1)$-client work.
This repository contains the simulator of *RouterORAM*, which is written in Rust language.


This README instructs how to run this simulator in Linux (or macOS) terminal.

## Install Rust and Cargo
Our simulator depends on Rust package, [Cargo](https://doc.rust-lang.org/cargo/index.html).
So, at first please install Rust and Cargo in your system by following [these steps](https://doc.rust-lang.org/cargo/getting-started/installation.html).


## Run Simulator with command line arguments
To run the simulator go to the ***oram_simulation*** directory of the downloaded version of this repository.
Then issue the following command:
```
RUSTFLAGS=-Awarnings cargo run --release -- <Argument 1 <Argument 2> <Argument 3> <Argument 4> &
```
**Explanation of the arguments:**
- **Argument 1:** Number of leaves in the ORAM tree, N
- **Argument 2:** Number of slots in each bucket, Z
- **Argument 3:** The ratio: $\frac{Total\ time\ of\ a\ day}{Time\ required\ to\ perform\ client\ requested\ I/O\ in\ a\ 40MB/s\ disk}$.

   This parameter decides the average daily remote data usage amount during simulation.
   For example, you want to simulate the behavior of *RouterORAM*, when on average the client daily accesses 800MB or remote data. Then total I/O time for accessing 800MB data on the 40MB/s disk would be: $\frac{800MB}{40MB/s}$ = 20seconds.
   So, in this case, the value of the **argument 3** would be:$\frac{24\times 60\times 60}{20}=4320$.
- **Argument 4:** Total number of simulation steps.

    **Note:** To get stable result, significantly large value is required to be used (e.g., $2^{37}$ or larger)

Following is an example of running our simulator, which simulates the behavior of *RouterORAM* with $N=4096$, $Z=64$, average daily remote access amount: $800MB$ and the number of simulation steps: $2^{37}$.
```
RUSTFLAGS=-Awarnings cargo run --release -- 4096 64 4320 137438953472&
```
After running this, it should show somthing like the following in the terminal:
```
     Running `target/release/oram_simulation 4096 64 4320 137438953472`
ORAM experiment started at: 2024-09-09_08-45-27
===================================================================================================================
ORAM experiment parameters: N = 4096, Z = 64, rate_ratio = 1, max_burst_cnt = 1, min_relax_cnt = 4320, ITR_CNT = 137438953472
===================================================================================================================
**** Last updated at: 2024-09-09_15:28:45, 64 % simulation done (tu = 87241796507 out of 137438953472), current statistics is:
-----------------------------------------------------------------------------------------------------------------------
Remove failure count: 4211625(2.545221022663567 %)
Insert failure count: 13144173(7.53660522088244 %)
Routing congestion count: 8856269361(10.151406453774024 %)
Total number of removals: 161260252
Total number of placements: 161249858(99.99355451831988 %)
```
The simulation may take significant amount of time, depending on the number of simulation steps. However, the simulation will keep updating current statistics in the terminal and also keep all statistics in csv format in a newly created directory under ***Logs***-folder.