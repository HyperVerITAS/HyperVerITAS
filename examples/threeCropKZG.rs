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

// use plonkish_backend::{
//     halo2_curves::bn256::{Bn256, Fr as FriFR},
//     pcs::{
//         multilinear::{blaze::commit, MultilinearBrakedown, ZeromorphFri },
//         univariate::{Fri, FriProverParams, FriVerifierParams},
//         Evaluation, // multilinear::MultilinearPolynomial
//         PolynomialCommitmentScheme as _,
//     },
//     poly::{multilinear::MultilinearPolynomial, Polynomial},
//     util::{
//         code::{Brakedown, BrakedownSpec6}, hash::Blake2s, transcript::{
//             InMemoryTranscript, 
//             Keccak256Transcript,
//         }
        
//     },
// };
// use util::{
//     hash::Blake2s};
// type Pcs = MultilinearBrakedown<FriFR, Blake2s, BrakedownSpec6>;

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


fn get_filename(prefix: &str, size: &usize, postfix: &str) -> String {
    let mut filename = prefix.to_owned();
    filename.push_str(&size.to_string());
    filename.push_str(postfix);
    filename.push_str(".txt");
    return filename
}

fn read_photo(prefix: &str, size:usize, postfix: &str) -> BufReader<File> {
    let file = File::open(get_filename(prefix, &size, postfix)).expect("Unable to open file");
    return BufReader::new(file);
}

fn main() {
    let testSize = 20;

    let mut rng = test_rng();
    // let numCols = ((testSize * 1000) as f64).log2().ceil() as usize;
    let numCols = testSize;

    // let numCols = 17;

    let cropNumRows = 22;
    let numRows = 7;
    let length = numCols + 1;
    

    // FRI SETUP----------------------------------------------------------------------------------------------------------
    
    
    let fileName = format!("test/Timings{}.json", testSize);
    let srs = PCS::gen_srs_for_testing(&mut rng, length).unwrap();
    let (pcs_param, ver_param) = PCS::trim(&srs, None, Some(length)).unwrap();
    for iii in 0..1 {
        // LOAD IMAGE----------------------------------------------------------------------------------------------------------
        let origImg = load_image(&fileName);
        println!("this is dim {:?}", origImg.cols * origImg.rows);
        //Below we do padding, prover works with padded image, but later sends the unpadded commitment to verifier (this is fine as unpadded effectively has padding as 0)
        let mut RGBEvals = [toFieldVec(&origImg.R),toFieldVec(&origImg.G),toFieldVec(&origImg.B)];
   
        //We implement padding
        for i in 0..(RGBEvals[0].len().next_power_of_two() - RGBEvals[0].len()) {
            RGBEvals[0].push(F::zero());
            RGBEvals[1].push(F::zero());
            RGBEvals[2].push(F::zero());

        }
        //THIS IS HASHING MATRIX CREATED BY CAMERA------------------------------------------------------------
        
        //THIS IS PROVER DOING EVERYTHING
        let now0 = Instant::now();
        let origImg = load_image(&fileName);
        let mut polies = Vec::new();
        let (origImgRPoly, _) = vec_to_poly(toFieldVec::<F>(&origImg.R));
        let (origImgGPoly, _) = vec_to_poly(toFieldVec::<F>(&origImg.G));
        let (origImgBPoly, _) = vec_to_poly(toFieldVec::<F>(&origImg.B));

        polies.push(origImgRPoly.clone());
        polies.push(origImgGPoly.clone());
        polies.push(origImgBPoly.clone());

        let now2 = Instant::now();
        let mut coms = Vec::new();
        for i in 0..polies.len(){
            coms.push(PCS::commit(&pcs_param,&polies[i].clone()).unwrap().clone());
        }

        let elapsed_time = now2.elapsed();
        let KZGCOMTIME= elapsed_time.as_millis() as f64 / 1000 as f64;
        println!("KZG COMMIT TIME IS {:?} seconds", KZGCOMTIME);
        let nowOpens = Instant::now();



        let mut transcript =
            <PolyIOP<F> as ProductCheck<Bls12_381, MultilinearKzgPCS<Bls12_381>>>::init_transcript(
            );
        let mut transcriptVerifier =
            <PolyIOP<F> as ProductCheck<Bls12_381, MultilinearKzgPCS<Bls12_381>>>::init_transcript(
            );

        for i in 0..3{
            transcript.append_serializable_element(b"img(x)", &coms[i]);
            transcriptVerifier.append_serializable_element(b"img(x)", &coms[i]);
        }


        // TIME THE IOP------------------------------------------------------------------------------------
       
        //-----------------------------------------------------------------------------------CROPPING--------------------------------------------------------------------------------------------
        let now: Instant = Instant::now();

        let cropFileName = format!("test/Crop{}.json", testSize);

        let cropImg = load_image(cropFileName);

       
        let (cropImgPolyR, _)  = vec_to_poly(toFieldVec::<F>(&cropImg.R));
        let (cropImgPolyG, _)  = vec_to_poly(toFieldVec::<F>(&cropImg.G));
        let (cropImgPolyB, _)  = vec_to_poly(toFieldVec::<F>(&cropImg.B));

        // origImg.cols * origImg.rows
        let (cropStartX,cropStartY) = (0,0);
        // println!("Made it");
        let transProofs = cropProveAffineIOP::<F>(numCols,cropNumRows, origImgRPoly.clone(), origImgGPoly.clone(),origImgBPoly.clone(), cropImgPolyR, cropImgPolyG, cropImgPolyB, origImg.cols, origImg.rows,
            cropStartX,cropStartY, cropStartX+numCols, cropStartY+numRows, &mut transcript);
        let elapsed_time = now.elapsed();
        println!(
            "Prover time to do crop IOP is {:?} seconds",
            elapsed_time.as_millis() as f64 / 1000 as f64
        );
        // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT H--------------------------------------------------------------------------------------------------------------------------
        // let nowOpens = Instant::now();

        // let friPolyComs = Pcs::batch_commit(&pp, &friPolies);
        // let elapsed_time = nowOpens.elapsed();
        // println!("FRI: Time to do COMMITMENTS FOR h, prod, frac, for FRI is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
        // allFriTimes += elapsed_time.as_millis() as f64 / 1000 as f64;

        // // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT END--------------------------------------------------------------------------------------------------------------------------
        // // --------------------------------------------------------------------------------------------------------------------------FRI OPENINGS--------------------------------------------------------------------------------------------------------------------------

        // //We now do some ridiculous openings (13)
        // //WE GET POINTS.
      
        let mut points = Vec::new();
        // let mut evals = Vec::new();
        // ----------------------------------------------START OF MAKING EVAL POINTS----------------------------------------------
      
        // 0 vector, used for h
    
        for i in 0..3{
            let origPt: Vec<F> = transProofs[i].point.clone();
            // println!("{:?}", proofR.point);
            points.push(origPt);
        }
        // ----------------------------------------------END OF MAKING EVAL POINTS----------------------------------------------
        let mut evalPols = Vec::new();
        let mut evalPoints = Vec::new();
        let mut evalVals = Vec::new();
        let mut evalComs = Vec::new();


        
        for i in 0..3{
            let polIndex = i;
            let ptIndex = i;
            evalPols.push(polies[polIndex].clone());
            evalPoints.push(points[ptIndex].clone());
            evalVals.push(polies[polIndex].evaluate(&points[ptIndex]).unwrap());
            evalComs.push(coms[polIndex].clone());
        }
        println!("MADE IT TO little openings");

        // println!("POLY LEN {}", polynomials.len());
        // println!("COM LEN {}", coms.len());
        // println!("POINTS LEN {}", points.len());
        // println!("EVALS LEN {}", evals.len());
        
        transcriptVerifier = transcript.clone();
            

        let openProofs = PCS::multi_open(&pcs_param,&evalPols,&evalPoints,&evalVals,&mut transcript).unwrap();


        let elapsed_time = nowOpens.elapsed();
        println!("KZG: Time to do openings for KZG is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);

        let elapsed_time = now0.elapsed();
        println!("Time to do WHOLE PROVER TIME is {:?} seconds", (elapsed_time.as_millis() as f64 / 1000 as f64)-KZGCOMTIME);


    //     //-----------------------------------------------------------------------------------START OF VERIFIER WORK:-------------------------------------------------------------------------------
    //     // //Verify hash pre-image   
        let now = Instant::now();
        PCS::batch_verify(&ver_param,&evalComs,&evalPoints,&openProofs,&mut transcriptVerifier).unwrap();

        let elapsed_time = now.elapsed();
        println!("Time to do VER OPENINGS TIME is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);

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
