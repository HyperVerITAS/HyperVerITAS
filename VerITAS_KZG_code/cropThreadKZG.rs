#![allow(warnings)]

use anyhow::Result;
use plonky2::field::types::Field;
use plonky2::iop::witness::{PartialWitness, WitnessWrite};
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::circuit_data::CircuitConfig;
use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
use std::time::{SystemTime, UNIX_EPOCH, Instant};
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::env;


fn print_time_since(last: u128, tag: &str) -> u128 {
    let now = SystemTime::now();
    let now_epoc = now
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let now = now_epoc.as_millis();
    println!("{:?} - time since last check: {:?}", tag, (now - last) as f64 / 1000 as f64); 
    return now;
} 

fn get_filename(prefix: &str, size: &usize, postfix: &str) -> String {
    let mut filename = prefix.to_owned();
    filename.push_str(&size.to_string());
    filename.push_str(postfix);
    filename.push_str(".txt");
    return filename
}

fn read_photo(prefix: &str,  size: usize, postfix: &str) -> BufReader<File> {
    let file = File::open(get_filename(prefix, &size, postfix)).expect("Unable to open file");
    return BufReader::new(file);
}

pub fn cropSystem(size: usize) -> Result<()> {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;

    // Timing setup
    let start = SystemTime::now();
    let start_epoch = start
        .duration_since(UNIX_EPOCH)
        .expect("Time went backwards");
    let start = start_epoch.as_millis();
    let mut last = start;

    let mut w_r_vals = Vec::new();
    let mut w_g_vals = Vec::new();
    let mut w_b_vals = Vec::new();
    let mut x_r_vals = Vec::new();
    let mut x_g_vals = Vec::new();
    let mut x_b_vals = Vec::new();

    let file = read_photo("Veri", size, "R");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<u32>().unwrap();
            w_r_vals.push(i as u32);
    }
    let file = read_photo("Veri", size, "G");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<u32>().unwrap();
            w_g_vals.push(i as u32);
    }
    let file = read_photo("Veri", size, "B");
    for line in file.lines() {
        let line = line.expect("Unable to read line");
        let i = line.parse::<u32>().unwrap();
            w_b_vals.push(i as u32);
    }

    let OLD_SIZE = 1<<size;
    let NEW_SIZE = 1<<(size-1);

    for i in 0..NEW_SIZE {
        x_r_vals.push(w_r_vals[i]);
        x_g_vals.push(w_g_vals[i]);
        x_b_vals.push(w_b_vals[i]);
    }

    last = print_time_since(last, "values generated"); 
   
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);

    let mut pw = PartialWitness::new();

    let mut w_r_targets = Vec::new();
    let mut w_g_targets = Vec::new();
    let mut w_b_targets = Vec::new();

    for i in 0..OLD_SIZE {
        let r = builder.add_virtual_target();
        w_r_targets.push(r);
        if i < NEW_SIZE {
            builder.register_public_input(r);
        }

        let g = builder.add_virtual_target();
        w_g_targets.push(g);
        if i < NEW_SIZE {
            builder.register_public_input(g);
        }
        
        let b = builder.add_virtual_target();
        w_b_targets.push(b);
        if i < NEW_SIZE {
            builder.register_public_input(b);  
        }     
    }
        
    let data = builder.build::<C>();
    last = print_time_since(last, "setup done"); 

    for i in 0..OLD_SIZE {
        pw.set_target(w_r_targets[i], F::from_canonical_u32(w_r_vals[i]));
        pw.set_target(w_g_targets[i], F::from_canonical_u32(w_g_vals[i]));
        pw.set_target(w_b_targets[i], F::from_canonical_u32(w_b_vals[i]));
    }

    let proof = data.prove(pw)?;
    last = print_time_since(last, "proof done");

    let res = data.verify(proof);
    let res = res.unwrap();

    last = print_time_since(last, "verify done");

    Ok(())
}

fn main (){
    let args: Vec<String> = env::args().collect();

    let first_size = args[1].parse::<usize>().unwrap();
    let mut last_size = first_size;
    if args.len() == 3{
        last_size = args[2].parse::<usize>().unwrap();
    }

    for i in first_size..last_size+1 {
        println!("Three Channel Crop, VerITAS KZG. Size: 2^{:?}\n", i);
        let now = Instant::now();
        let _res = cropSystem(i);
        let elapsed_time = now.elapsed();
        println!("Whole Time: {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
        println!("-----------------------------------------------------------------------");
    }
}