// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.

#![allow(warnings)]

use ark_ec::pairing::Pairing;
use core::num;
use std::{ops::Deref, primitive, str::FromStr, time::Instant};

use ark_bls12_381::{Bls12_381, Fq, Fr, G1Affine, G2Affine};
use ark_ff::{Field, Fp, Fp2, PrimeField, UniformRand, Zero};
use subroutines::{
    pcs::{
        self,
        prelude::{Commitment, MultilinearKzgPCS, PolynomialCommitmentScheme},
    },
    poly_iop::{
        prelude::{PermutationCheck, ProductCheck, SumCheck, ZeroCheck},
        PolyIOP,
    },
    BatchProof, MultilinearProverParam, PolyIOPErrors,
};
// use crate::poly_iop::{
//     prelude::{PermutationCheck, ZeroCheck, SumCheck},
//     errors::PolyIOPErrors,
//     structs::{IOPProof, IOPProverState, IOPVerifierState},
//     PolyIOP,
// };
use arithmetic::{eq_eval, merge_polynomials, random_mle_list, VPAuxInfo, VirtualPolynomial};
pub use ark_poly::{DenseMultilinearExtension, MultilinearExtension};
use ark_std::{
    end_timer,
    rand::{self, RngCore},
    start_timer,
};
use proc_status::ProcStatus;
use std::{marker::PhantomData, sync::Arc};
use transcript::IOPTranscript;
use std::env;

// use ark_test_curves::bls12_381::Fq as F;
use ark_bls12_381::Fr as F;
type PCS = MultilinearKzgPCS<Bls12_381>;
use ark_ff::One;
use ark_std::{rand::RngCore as R, test_rng};
use itertools::Itertools;
mod helper;
use helper::*;
mod image;
use image::*;
mod protocols;
use protocols::*;
mod prover;
use prover::*;
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;
use plonkish_backend::{
    halo2_curves::bn256::{Bn256, Fr as A},
    pcs::{
        multilinear::{ZeromorphFri, MultilinearBrakedown },
        univariate::{Fri, FriProverParams, FriVerifierParams},
        Evaluation, // multilinear::MultilinearPolynomial
        PolynomialCommitmentScheme as _,
    },
    poly::{multilinear::MultilinearPolynomial, Polynomial},
    // piop::,
    util::{
        arithmetic::Field as myField,
        goldilocksMont::GoldilocksMont as FriFR,
        hash::Blake2s,
        transcript::{
            InMemoryTranscript, 
            Keccak256Transcript,
        },
        code::{Brakedown, BrakedownSpec6},
        
    },
};
// use util::{
//     hash::Blake2s};
type Pcs = MultilinearBrakedown<FriFR, Blake2s, BrakedownSpec6>;

// type Pcs = MultilinearBrakedown<FriFR, Blake2s, BrakedownSpec6>;
// Use fri

const irredPolyTable: &[u32] = &[
    0, 0, 7, 11, 19, 37, 67, 131, 285, 529, 1033, 2053, 4179, 8219, 16707, 32771, 69643, 131081,
    262273, 524327, 1048585, 2097157, 4194307, 8388641, 16777351, 33554441, 67108935,
];
// use rand_seeder::{Seeder, SipHasher};
// use rand_pcg::Pcg64;

//For nv = 15, we should do polyforT 32771 with corresponding 69643
//For nv = 10, we should do polyforT 1033 with corresponding 2053
//For nv = 11, we should do polyforT 2053 with corresp 4179
//We just now add
//13 corresp 8219
//14 corresp 16707
// 9 corresp 529
//8 corresp 285
//We pad with 0s for deg 0 and deg 1, as no prim poly for those...

const X: u128 = 3091352403337663489;
const A_CONSTANT: u128 = 3935559000370003845;
const C_CONSTANT: u128 = 2691343689449507681;

fn kzgFieldToFriField(kzg: &F) -> FriFR {
    // let bytes: [u64; 4] = kzg.0.0;
    // let mem: [u8; 32] =;
    // let fri =
    // fri
    let mut buf: [u64; 4] = unsafe { std::mem::transmute(kzg.0 .0) };
    // buf[31] = 0;
    FriFR::from(buf[0])
}

fn run_hash_com_kzg(testSize: usize) {
    let mut rng = test_rng();

    let numCols = testSize;
    let cropNumRows = testSize-1;
    let numRows = 7;
    let length = numCols + 1;
    

    // FRI SETUP----------------------------------------------------------------------------------------------------------
    let (pp, vp) = {
        let poly_size = 1 << length;
        let param = Pcs::setup(poly_size, 1, &mut rng).unwrap();
        Pcs::trim(&param, poly_size, 4).unwrap()
    };
    println!("MADE IT");


    let mut transcriptFri = Keccak256Transcript::new(());

    // println!("Test successful");
    let fileName = format!("test/Timings{}.json", testSize);
    let srs = PCS::gen_srs_for_testing(&mut rng, length).unwrap();
    let (pcs_param, ver_param) = PCS::trim(&srs, None, Some(length)).unwrap();

    //THIS IS PROVER DOING EVERYTHING
    let now = Instant::now();
    let origImg = load_image(&fileName);
    let imgPolyR = vec_to_poly(toFieldVec(&origImg.R)).0;
    let imgPolyG = vec_to_poly(toFieldVec(&origImg.G)).0;
    let imgPolyB = vec_to_poly(toFieldVec(&origImg.B)).0;
    
    let now2 = Instant::now();
    let img_comR = PCS::commit(pcs_param.clone(), &imgPolyR).unwrap();
    let img_comG = PCS::commit(pcs_param.clone(), &imgPolyG).unwrap();
    let img_comB = PCS::commit(pcs_param.clone(), &imgPolyB).unwrap();
    let elapsed_time = now2.elapsed();
    println!("KZG COMMIT TIME IS {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
}

fn main(){
    let args: Vec<String> = env::args().collect();

    let first_size = args[1].parse::<usize>().unwrap();
    let mut last_size = first_size;
    if args.len() == 3{
        last_size = args[2].parse::<usize>().unwrap();
    }

    for i in first_size..last_size+1 {
        println!("Hash Commitment KZG. Size: 2^{:?}\n", i);
        let _res = run_hash_com_kzg(i);
        println!("-----------------------------------------------------------------------");
    }
}