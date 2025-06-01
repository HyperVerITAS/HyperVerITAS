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
use std::io::{BufRead, BufReader};
use std::fs::File;
use std::env;

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

fn get_filename(prefix: &str, postfix: &str, mySize: &usize) -> String {
    let mut filename = "test/".to_owned();

    filename.push_str(&prefix.to_owned());
    // filename.push_str("image_");
    filename.push_str(&mySize.to_string());
    // filename.push_str("_");
    // filename.push_str(&EXPONENT.to_string());
    filename.push_str(postfix);

    filename.push_str(".txt");
    return filename
}

fn read_photo(prefix: &str,  postfix: &str, mySize: &usize) -> BufReader<File> {
    let file = File::open(get_filename(prefix, postfix, mySize)).expect("Unable to open file");
    return BufReader::new(file);
}

fn run_one_crop(size: usize) {
    println!("One Channel Crop , HyperVerITAS Brakedown. Size: 2^{:?}\n", size);

    let mut rng = test_rng();

    let numCols = size;
    let numRows = 7;
    
    let cropNumRows = size-1;
    let length = numCols;
    

    // FRI SETUP----------------------------------------------------------------------------------------------------------
    let (pp, vp) = {
        let poly_size = 1 << length;
        let param = Pcs::setup(poly_size, 1, &mut rng).unwrap();
        Pcs::trim(&param, poly_size, 4).unwrap()
    };


    let mut transcriptFri = Keccak256Transcript::new(());

    // println!("Test successful");
    let srs = PCS::gen_srs_for_testing(&mut rng, length).unwrap();
    let (pcs_param, ver_param) = PCS::trim(&srs, None, Some(length)).unwrap();
    for iii in 0..1 {
        // LOAD IMAGE----------------------------------------------------------------------------------------------------------
        let file = read_photo("Veri", "R", &size);
        let mut origImg = Vec::<u8>::new();
        for line in file.lines() {
            let line = line.expect("Unable to read line");
            let i = line.parse::<u8>().unwrap();
            origImg.push(i);
        }

        //Below we do padding, prover works with padded image, but later sends the unpadded commitment to verifier (this is fine as unpadded effectively has padding as 0)
        let mut REvals = toFieldVec::<F>(&origImg);
        let mut REvalsFri = toFieldVecFri::<FriFR>(&origImg.iter().map(|&x| x as u64).collect::<Vec<_>>());

        //We implement padding
        // for i in 0..(RGBEvalsFri[0].len().next_power_of_two() - RGBEvalsFri[0].len()) {
        
        
        //THIS IS PROVER DOING EVERYTHING
        let now = Instant::now();
        let file = read_photo("Veri", "R", &size);
        let mut origImg = Vec::<u8>::new();
        for line in file.lines() {
            let line = line.expect("Unable to read line");
            let i = line.parse::<u8>().unwrap();
            origImg.push(i);
        }

        let BLANK = vec_to_poly(vec![F::zero();1<<size]).0;
        let now2 = Instant::now();

        let img_comR = PCS::commit(pcs_param.clone(), &BLANK).unwrap();
        let elapsed_time = now2.elapsed();
        println!("KZG COMMIT TIME IS {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
        // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT IMG--------------------------------------------------------------------------------------------------------------------------

        let mut transcriptFri = Keccak256Transcript::new(());

        let mut imgPoliesFri: Vec<MultilinearPolynomial<FriFR>> = Vec::new();
        
        imgPoliesFri.push(MultilinearPolynomial::<FriFR>::from_evals(REvalsFri.clone()));

        let imgPolyFriCom = Pcs::batch_commit(&pp, &imgPoliesFri).unwrap();

        // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT END--------------------------------------------------------------------------------------------------------------------------

        let mut transcript =
            <PolyIOP<F> as ProductCheck<Bls12_381, MultilinearKzgPCS<Bls12_381>>>::init_transcript(
            );
        let mut transcriptVerifier =
            <PolyIOP<F> as ProductCheck<Bls12_381, MultilinearKzgPCS<Bls12_381>>>::init_transcript(
            );

        // for i in 0..3{
        transcript.append_serializable_element(b"img(x)", &img_comR);
        transcriptVerifier.append_serializable_element(b"img(x)", &img_comR);
        // }


        // TIME THE IOP------------------------------------------------------------------------------------
       
        //-----------------------------------------------------------------------------------CROPPING--------------------------------------------------------------------------------------------

        let cropFile = read_photo("Crop", "R", &size);
        let mut cropImg = Vec::<u8>::new();
        let mut rows:usize = 0;
        let mut cols:usize = 0;
        let mut count = 0;
        for line in cropFile.lines() {
            let line = line.expect("Unable to read line");
            if(count == 0){
                let i = line.parse::<usize>().unwrap();
                rows = i;
                count += 1;
            }else if(count == 1){
                let i = line.parse::<usize>().unwrap();
                cols = i;
                count +=1;
            }else{
                let i = line.parse::<u8>().unwrap();
                cropImg.push(i);
            }
        }

        let (origImgRPoly, _) = vec_to_poly(toFieldVec::<F>(&origImg));

        let (cropImgPolyR, _)  = vec_to_poly(toFieldVec::<F>(&cropImg));

        // origImg.cols * origImg.rows
        let (cropStartX,cropStartY) = (0,0);
        // println!("Made it");
        let transProofs = cropProveOneAffineIOP::<F>(numCols,cropNumRows, origImgRPoly, cropImgPolyR, cols.into(), rows.into(),
            cropStartX,cropStartY, cropStartX+numCols, cropStartY+numRows, &mut transcript);
        let elapsed_time = now.elapsed();
        println!(
            "Prover time to do crop IOP is {:?} seconds",
            elapsed_time.as_millis() as f64 / 1000 as f64
        );
        // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT H--------------------------------------------------------------------------------------------------------------------------

        // let elapsed_time = nowOpens.elapsed();
        // println!("FRI: Time to do COMMITMENTS FOR h, prod, frac, for FRI is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
        // allFriTimes += elapsed_time.as_millis() as f64 / 1000 as f64;

        // // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT END--------------------------------------------------------------------------------------------------------------------------
        // // --------------------------------------------------------------------------------------------------------------------------FRI OPENINGS--------------------------------------------------------------------------------------------------------------------------


        // //We now do some ridiculous openings (13)
        // //WE GET POINTS.
        let mut polynomials = imgPoliesFri;
        let mut coms = imgPolyFriCom;
        let mut points = Vec::new();
        let mut evals = Vec::new();
        // ----------------------------------------------START OF MAKING EVAL POINTS----------------------------------------------
      
        let mut origPt: Vec<FriFR> = transProofs.point.iter().map(|x| kzgFieldToFriField(x)).collect();
        // println!("{:?}", proofR.point);
        points.push(origPt.clone());
        // ----------------------------------------------END OF MAKING EVAL POINTS----------------------------------------------
        
       
        // //----------------------------------------------We first add opening for matrixMult for hash.----------------------------------------------    
   
            // // // //----------------------------------------------we now add transPoint for IMG ----------------------------------------------
        evals.push(Evaluation::new(
            0, //This is the poly index
            0, //This is the point index
            polynomials[0].evaluate(&points[0]),
        ));
        
        // println!("MADE IT TO little openings");

        // println!("POLY LEN {}", polynomials.len());
        // println!("COM LEN {}", coms.len());
        // println!("POINTS LEN {}", points.len());
        // println!("EVALS LEN {}", evals.len());

        Pcs::batch_open(
            &pp,
            &polynomials,
            &coms,
            &points,
            &evals,
            &mut transcriptFri,
        ).unwrap();

        let elapsed_time = now.elapsed();
        println!("Time to do WHOLE PROVER TIME is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
        println!("-----------------------------------------------------------------------");

    //     // --------------------------------------------------------------------------------------------------------------------------END OF FRI OPENINGS--------------------------------------------------------------------------------------------------------------------------

    //     //-----------------------------------------------------------------------------------START OF VERIFIER WORK:-------------------------------------------------------------------------------
    //      
    // let now = Instant::now();
    // let mut transcriptFri = Keccak256Transcript::new(());
// 
    // Pcs::batch_verify(
    //     &vp,
    //     &coms,
    //     &points,
    //     &evals,
    //     &mut transcriptFri,
    // ).unwrap();     
    // let elapsed_time = now.elapsed();
    // println!("FRI: Time to do VERIFY IS {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
    // //Verify hash pre-image
    //     // let alpha = transcriptVerifier.get_and_append_challenge(b"alpha").unwrap();
    //     // let mut frievaldRandVec = Vec::new();

    //     // for i in 0 .. (1<<numRows){
    //     //     frievaldRandVec.push(alpha);
    //     // }
    //     // let mut mySum = F::zero();
    //     // for i in 0 .. (1<<numRows){
    //     //     mySum += frievaldRandVec[i] * testDigestR[i];
    //     // }
    //     // println!("THIS IS ALPHA, {}", alpha);
    //     // println!("THIS IS mySum, {}", mySum);

    //     // let subclaim = <PolyIOP<F> as SumCheck<F>>::verify(
    //     //     mySum,
    //     //     &proofR,
    //     //     &poly_info_matMult,
    //     //     &mut transcriptVerifier,
    //     // ).unwrap();
        
    }
}

fn main(){
    let args: Vec<String> = env::args().collect();

    let first_size = args[1].parse::<usize>().unwrap();
    let mut last_size = first_size;
    if args.len() == 3{
        last_size = args[2].parse::<usize>().unwrap();
    }

    for i in first_size..last_size+1 {
        run_one_crop(i);
    }
}
