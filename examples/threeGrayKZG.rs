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
use std::env;

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

// fn kzgFieldToFriField(kzg: &F) -> FriFR {
//     // let bytes: [u64; 4] = kzg.0.0;
//     // let mem: [u8; 32] =;
//     // let fri =
//     // fri
//     let mut buf: [u8; 32] = unsafe { std::mem::transmute(kzg.0 .0) };
//     buf[31] = 0;
//     FriFR::from_bytes(&buf).unwrap()
// }

fn hashPreimageIOP<F: PrimeField, E, PCS>(
    numCols: usize,
    numRows: usize,
    RGBEvals: [Vec<F>;3],
    transcript: &mut IOPTranscript<E::ScalarField>,
    pcs_param: &PCS::ProverParam,
    ver_param: &PCS::VerifierParam,
) -> (
    [<PolyIOP<F> as SumCheck<F>>::SumCheckProof;3],
    [VPAuxInfo<F>;3],
    // THERE HAS GOT TO BE A BETTER WAY SINCE WE KNOW ITS SIZE 3...
    Vec<<PolyIOP<E::ScalarField> as ProductCheck<E, PCS>>::ProductCheckProof>,
    Vec<Arc<DenseMultilinearExtension<F>>>,
    Vec<Arc<DenseMultilinearExtension<F>>>,
    Vec<Arc<DenseMultilinearExtension<F>>>,
)
where
    E: Pairing<ScalarField = F>,
    PCS: PolynomialCommitmentScheme<
        E,
        Polynomial = Arc<DenseMultilinearExtension<E::ScalarField>>,
        Point = Vec<F>,
        Evaluation = F,
    >,
{
    //We assume we use the randomness matrix.
    let mut rng = test_rng();
    let mut matrixA = Vec::new();
    for i in 0..128 {
        matrixA.push(ChaCha8Rng::seed_from_u64(i));
    }
    //We are given the image polynomial
    
    let mut imgPolies: Vec<Arc<DenseMultilinearExtension<F>>> = Vec::new();

    imgPolies.push(vec_to_poly::<F>(RGBEvals[0].clone()).0);
    imgPolies.push(vec_to_poly::<F>(RGBEvals[1].clone()).0);
    imgPolies.push(vec_to_poly::<F>(RGBEvals[2].clone()).0);
    //We make Frievald random vec

    let mut frievaldRandVec = Vec::new();

    for i in 0..(1 << numRows) {
        let alpha = transcript.get_and_append_challenge(b"alpha").unwrap();

        frievaldRandVec.push(alpha);
    }
    // let frievaldRand = Arc::new(DenseMultilinearExtension::rand(numCols, &mut rng));
    // let frievaldRandVec: &Vec<F>  = &frievaldRand.evaluations;

    //We make rT*A --------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    let now = Instant::now();

    let mut rTA = Vec::new();

    for i in 0..(1 << numCols) {
        let mut mySum = F::zero();
        for j in 0..128 {
            mySum += F::rand(&mut matrixA[j]) * frievaldRandVec[j];
        }
        rTA.push(mySum);
    }

    let (rTAPoly, _) = vec_to_poly::<F>(rTA.clone());
    let elapsed_time = now.elapsed();
    println!(
        "Prover time to do rTA is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    //We run the sumcheck on rTA * I------------------------------------------------------------------------------------------------------------------------------------------------------------
    let now = Instant::now();
    let mut RHS_RGB = Vec::new();
    for i in 0..3{
        RHS_RGB.push(VirtualPolynomial::new_from_mle(&rTAPoly, F::one()));
        RHS_RGB[i].mul_by_mle(imgPolies[i].clone(), F::one());
    }
    // RHS_RGB.mul_by_mle(imgPoly.clone(), F::one());

    // WE CAN BATCH THIS...
    // let alpha1 = transcript.get_and_append_challenge(b"alpha").unwrap();

    // let alpha2 = transcript.get_and_append_challenge(b"alpha").unwrap();

    // let mySumPoly = &RHS_RGB[0] + alpha1*&RHS_RGB[1]+alpha2*&RHS_RGB[0];
    let proofRGB = [<PolyIOP<F> as SumCheck<F>>::prove(&RHS_RGB[0], transcript).unwrap(),
        <PolyIOP<F> as SumCheck<F>>::prove(&RHS_RGB[1], transcript).unwrap(),
        <PolyIOP<F> as SumCheck<F>>::prove(&RHS_RGB[2], transcript).unwrap()];
    
    let poly_infoRGB = [RHS_RGB[0].aux_info.clone(),
        RHS_RGB[1].aux_info.clone(),
        RHS_RGB[2].aux_info.clone()];
    
    let elapsed_time = now.elapsed();
    println!(
        "Prover time to do Sumcheck for hash preimage is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    let mut mySum = F::zero();

    //We run range check on image-----------------------------------------------------------------------------------------------------------------------------------------------------------------------
    let now = Instant::now();
    let (mut multsetProofRGB, mut fxRGB, mut gxRGB, mut hRGB) = (Vec::new(),Vec::new(),Vec::new(),Vec::new());
    for i in 0..3{
        let (multsetProof, fx, gx, h) = range_checkProverIOP::<F, E, PCS>(
        numCols,
        255.try_into().unwrap(),
        imgPolies[i].clone(),
        irredPolyTable[numCols].try_into().unwrap(),
        irredPolyTable[numCols].try_into().unwrap(),
        transcript,
        &pcs_param,
        &ver_param,
        );
        multsetProofRGB.push(multsetProof);
        fxRGB.push(fx);
        gxRGB.push(gx);
        hRGB.push(h);
    }
    let elapsed_time = now.elapsed();
    println!(
        "Prover time to do MultCheck for hash preimage is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );

    //We return a vector containing the final points to evaluate I, the final points to evaulate h(from range check), the final points
    //to evaluate the prod and frac polynomials, as well as the sumcheck proof, range check proof.
    return (proofRGB, poly_infoRGB, multsetProofRGB, fxRGB, gxRGB, hRGB);
}

fn run_three_channel_gray(testSize: usize) {
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
        // println!("this is dim {:?}", origImg.cols * origImg.rows);
        //Below we do padding, prover works with padded image, but later sends the unpadded commitment to verifier (this is fine as unpadded effectively has padding as 0)
        let mut RGBEvals = [toFieldVec(&origImg.R),toFieldVec(&origImg.G),toFieldVec(&origImg.B)];
   
        //We implement padding
        for i in 0..(RGBEvals[0].len().next_power_of_two() - RGBEvals[0].len()) {
            RGBEvals[0].push(F::zero());
            RGBEvals[1].push(F::zero());
            RGBEvals[2].push(F::zero());

        }
        //THIS IS HASHING MATRIX CREATED BY CAMERA------------------------------------------------------------
        let mut testDigestRGB = Vec::new();
        for k in 0 ..2{
            let mut matrixA = Vec::new();
            for i in 0..128 {
                matrixA.push(ChaCha8Rng::seed_from_u64(i));
            }
            //THIS IS HASHING DONE BY CAMERA------------------------------------------------------------
            let mut testDigest = Vec::new();
            for i in 0..128 {
                let mut mySum = F::zero();
                for j in 0..(1 << numCols) {
                    // mySum +=  RGBEvalsFri[k][j];
                    // PLACEHOLDER UNTIL I FIGURE OUT RANDOMNESS
                    mySum += F::rand(&mut matrixA[i]) * RGBEvals[k][j];
                }
                testDigest.push(mySum);
            }
            testDigestRGB.push(testDigest);
        }

        let mut transcript =
            <PolyIOP<F> as ProductCheck<Bls12_381, MultilinearKzgPCS<Bls12_381>>>::init_transcript(
            );
        let mut transcriptVerifier =
            <PolyIOP<F> as ProductCheck<Bls12_381, MultilinearKzgPCS<Bls12_381>>>::init_transcript(
            );

        //THIS IS PROVER DOING EVERYTHING

        let now: Instant = Instant::now();
        let origImg = load_image(&fileName);
        let mut polies = Vec::new();
        polies.push(vec_to_poly(toFieldVec(&origImg.R)).0);
        polies.push( vec_to_poly(toFieldVec(&origImg.G)).0);
        polies.push( vec_to_poly(toFieldVec(&origImg.B)).0);

        //let now2 = Instant::now();
        let mut coms = Vec::new();
        for i in 0..polies.len(){
            coms.push(PCS::commit(&pcs_param,&polies[i].clone()).unwrap().clone());
        }

        //let elapsed_time = now2.elapsed();
        // println!("KZG COMMIT TIME IS {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
        // let nowOpens = Instant::now();
        //let now0 = Instant::now();

        for i in 0..3{
            transcript.append_serializable_element(b"img(x)", &coms[i]);
            transcriptVerifier.append_serializable_element(b"img(x)", &coms[i]);
        }


        // TIME THE IOP------------------------------------------------------------------------------------
       
        //-----------------------------------------------------------------------------------GRAYSCALE--------------------------------------------------------------------------------------------

        let grayFileName = format!("test/Gray{}.json", testSize);

        let grayImg = load_image(grayFileName);

        let (origImgRPoly, _) = vec_to_poly(toFieldVec::<F>(&origImg.R));
        let (origImgGPoly, _) = vec_to_poly(toFieldVec::<F>(&origImg.G));
        let (origImgBPoly, _) = vec_to_poly(toFieldVec::<F>(&origImg.B));

        let (grayImg, _)  = vec_to_poly(toFieldVec::<F>(&grayImg.R));
        // let (grayImgPolyG, _)  = vec_to_poly(toFieldVec::<F>(&grayImg.G));
        // let (grayImgPolyB, _)  = vec_to_poly(toFieldVec::<F>(&grayImg.B));

        // origImg.cols * origImg.rows
        
        // println!("Made it");
        let mut grayError = Vec::new();
        for i in 0..1<<numCols{
            grayError.push(F::from_le_bytes_mod_order(&[100])*grayImg.evaluations[i]-
            (F::from_le_bytes_mod_order(&[30])*origImgRPoly.evaluations[i]+
            F::from_le_bytes_mod_order(&[59])*origImgGPoly.evaluations[i]+
            F::from_le_bytes_mod_order(&[11])*origImgBPoly.evaluations[i]
            )
            +F::from_le_bytes_mod_order(&[100])
        );
        }
       
        // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT H--------------------------------------------------------------------------------------------------------------------------
        // let nowOpens = Instant::now();

        let mut polies2 = Vec::new();
       
        // Polies for grayscaling
      

     
        // let friPolyComs = Pcs::batch_commit(&pp, &friPolies);
        // let elapsed_time = nowOpens.elapsed();
        // println!("FRI: Time to do COMMITMENTS FOR h, prod, frac, for FRI is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
        // allFriTimes += elapsed_time.as_millis() as f64 / 1000 as f64;

        // // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT END--------------------------------------------------------------------------------------------------------------------------
        // // --------------------------------------------------------------------------------------------------------------------------FRI OPENINGS--------------------------------------------------------------------------------------------------------------------------

        // //We now do some ridiculous openings (13)
        // //WE GET POINTS.
       
        // START OF GRAYSCALE STUFF
        let (grayErrPoly, _) = vec_to_poly(grayError);
        let grayErrCom = PCS::commit(&pcs_param, &grayErrPoly).unwrap().clone();
        transcript.append_serializable_element(b"gray(x)", &grayErrCom);
        // Do range check for grayscale
        let (multsetProofGray, fxGray, gxGray, hGray) = range_checkProverIOP::<F, Bls12_381, MultilinearKzgPCS<Bls12_381>>(
        numCols,
        255.try_into().unwrap(),
        grayErrPoly.clone(),
        irredPolyTable[numCols].try_into().unwrap(),
        irredPolyTable[numCols].try_into().unwrap(),
        &mut transcript,
        &pcs_param,
        &ver_param,
        );
        // let elapsed_time = now.elapsed();
        // println!(
        //     "Prover time to do GRAYSCALE IOP is {:?} seconds",
        //     elapsed_time.as_millis() as f64 / 1000 as f64
        // );
        println!("out of IOP");
        // PUSH COMS FOR GRAYSCALE ERROR

        polies2.push(grayErrPoly);
        polies2.push(hGray.clone());
        polies2.push(gxGray);
        polies2.push(fxGray);

        coms.push(grayErrCom);
        let hGrayCom = PCS::commit(&pcs_param, &hGray).unwrap().clone();    
        coms.push(hGrayCom);
        coms.push(multsetProofGray.prod_x_comm);
        coms.push(multsetProofGray.frac_comm);

        // END OF GRAYSCALE COMS COMMITS
        let mut points = Vec::new();
        // let mut evals = Vec::new();
        // ----------------------------------------------START OF MAKING EVAL POINTS----------------------------------------------
        println!("starting eval");
        // 0 vector, used for h
        points.push(vec![F::zero(); numCols]);
        // 1..10 vector, used for prod 
        let mut final_query = vec![F::one(); numCols+1];
        final_query[0] = F::zero();
        points.push(final_query);
        
        // This is point for gray scale transformation
        let origPt = transcript.get_and_append_challenge_vectors(b"alpha", numCols).unwrap();
        // let origPt: Vec<F> = transProofs[i].point.clone();
        // println!("{:?}", proofR.point);
        points.push(origPt);
    

        //GRAYSCALE POINTS
        println!("THIS IS LEN OF PTS {}", points.len());
        let myRand = &multsetProofGray.zero_check_proof.point;
        
        let mut myRandSmall = Vec::new();
        for i in 0..myRand.len()-1{
            myRandSmall.push(myRand[i]);
        }
        // myRand.push(F::rand(&mut rng));
        points.push(myRandSmall.clone());
        // point 1 for h_{+1}
        myRandSmall[2] = F::one() - myRandSmall[2];
        points.push(myRandSmall.clone());
        // point 2 for h_{+1}
        myRandSmall[2] = F::one() - myRandSmall[3];
        points.push(myRandSmall.clone());
        //Rand point used for prod and frac polies 
        let mut ptRand= myRand.clone();
        points.push(ptRand.clone());
        // Randpoint but last is 0
        ptRand[numCols] = F::zero();
        points.push(ptRand.clone());
        // Randpoint but last is 1
        ptRand[numCols] = F::one();
        points.push(ptRand.clone());
        // ---------------------------------------------END OF MAKING EVAL POINTS----------------------------------------------
        let mut evalPols = Vec::new();
        let mut evalPoints = Vec::new();
        let mut evalVals = Vec::new();
        let mut evalComs = Vec::new();
        let mut evalPolsBig = Vec::new();
        let mut evalPointsBig = Vec::new();
        let mut evalValsBig = Vec::new();
        let mut evalComsBig = Vec::new();

        
        for i in 0..3{
        // //----------------------------------------------We first add opening for matrixMult for hash.----------------------------------------------     
            // // // //----------------------------------------------we now add transPoint for IMG ----------------------------------------------
            let polIndex = i;
            let ptIndex = 2;
            evalPols.push(polies[polIndex].clone());
            evalPoints.push(points[ptIndex].clone());
            evalVals.push(polies[polIndex].evaluate(&points[ptIndex]).unwrap());
            evalComs.push(coms[polIndex].clone());
        }
        
        //----------------------------------------------GRAYSCALE: We first add opening for transPoint for GRAY.----------------------------------------------    
        let polIndex = 0;
        let ptIndex = 2;
        evalPols.push(polies2[polIndex].clone());
        evalPoints.push(points[ptIndex].clone());
        evalVals.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComs.push(coms[polIndex+3].clone());
        // //----------------------------------------------GRAYSCALE: We now add 0 for h----------------------------------------------
        let polIndex = 1;
        let ptIndex = 0;
        evalPols.push(polies2[polIndex].clone());
        evalPoints.push(points[ptIndex].clone());
        evalVals.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComs.push(coms[polIndex+3].clone());

        // // //----------------------------------------------GRAYSCALE: We now add alpha_range for error----------------------------------------------
        let polIndex = 0;
        let ptIndex = 3;
        evalPols.push(polies2[polIndex].clone());
        evalPoints.push(points[ptIndex].clone());
        evalVals.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComs.push(coms[polIndex].clone());

        // // //----------------------------------------------GRAYSCALE: We now add alpha_range for h----------------------------------------------

        let polIndex = 1;
        let ptIndex = 3;
        evalPols.push(polies2[polIndex].clone());
        evalPoints.push(points[ptIndex].clone());
        evalVals.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComs.push(coms[polIndex+3].clone());
        // // //----------------------------------------------GRAYSCALE: We now add alpha_range modified0 for h----------------------------------------------

        let polIndex = 1;
        let ptIndex = 4;
        evalPols.push(polies2[polIndex].clone());
        evalPoints.push(points[ptIndex].clone());
        evalVals.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComs.push(coms[polIndex+3].clone());
        // // //----------------------------------------------GRAYSCALE: We now add alpha_range modified1 for h----------------------------------------------
        let polIndex = 1;
        let ptIndex = 5;
        evalPols.push(polies2[polIndex].clone());
        evalPoints.push(points[ptIndex].clone());
        evalVals.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComs.push(coms[polIndex+3].clone());
        
        // // //WE NOW DO BIG POLYNOMIALS --------------------------------------------------------------------------------------------
        // // //----------------------------------------------GRAYSCALE: We then add prod for 1...10----------------------------------------------
        let polIndex = 2;
        let ptIndex = 1;
        evalPolsBig.push(polies2[polIndex].clone());
        evalPointsBig.push(points[ptIndex].clone());
        evalValsBig.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComsBig.push(coms[polIndex+3].clone());
        
    
        // // //----------------------------------------------GRAYSCALE: We now add alpha_range for prod----------------------------------------------
        let polIndex = 2;
        let ptIndex = 6;
        evalPolsBig.push(polies2[polIndex].clone());
        evalPointsBig.push(points[ptIndex].clone());
        evalValsBig.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComsBig.push(coms[polIndex+3].clone());

        // // //----------------------------------------------GRAYSCALE: We now add alpha_range for frac----------------------------------------------

        let polIndex = 3;
        let ptIndex = 6;
        evalPolsBig.push(polies2[polIndex].clone());
        evalPointsBig.push(points[ptIndex].clone());
        evalValsBig.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComsBig.push(coms[polIndex+3].clone());
        // //----------------------------------------------GRAYSCALE: we now add alpha_range||0 for prod----------------------------------------------
        let polIndex = 2;
        let ptIndex = 7;
        evalPolsBig.push(polies2[polIndex].clone());
        evalPointsBig.push(points[ptIndex].clone());
        evalValsBig.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComsBig.push(coms[polIndex+3].clone());

        // // // // //----------------------------------------------GRAYSCALE: we now add alpha_range||0 for frac----------------------------------------------
        let polIndex = 3;
        let ptIndex = 7;
        evalPolsBig.push(polies2[polIndex].clone());
        evalPointsBig.push(points[ptIndex].clone());
        evalValsBig.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComsBig.push(coms[polIndex+3].clone());
        

        // // // //----------------------------------------------GRAYSCALE: we now add alpha_range||1 for prod----------------------------------------------
        let polIndex = 2;
        let ptIndex = 8;
        evalPolsBig.push(polies2[polIndex].clone());
        evalPointsBig.push(points[ptIndex].clone());
        evalValsBig.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComsBig.push(coms[polIndex+3].clone());


        // // // //----------------------------------------------GRAYSCALE: we now add alpha_range||1 for frac----------------------------------------------
        let polIndex = 3;
        let ptIndex = 8;
        evalPolsBig.push(polies2[polIndex].clone());
        evalPointsBig.push(points[ptIndex].clone());
        evalValsBig.push(polies2[polIndex].evaluate(&points[ptIndex]).unwrap());
        evalComsBig.push(coms[polIndex+3].clone());   
        // // // //----------------------------------------------DONE WITH OPENINGS ----------------------------------------------
  
        println!("MADE IT TO little openings");

        // println!("POLY LEN {}", polynomials.len());
        // println!("COM LEN {}", coms.len());
        // println!("POINTS LEN {}", points.len());
        // println!("EVALS LEN {}", evals.len());
        
        transcriptVerifier = transcript.clone();
            

        let openProofs = PCS::multi_open(&pcs_param,&evalPols,&evalPoints,&evalVals,&mut transcript).unwrap();
        let openProofsBig = PCS::multi_open(&pcs_param,&evalPolsBig,&evalPointsBig,&evalValsBig,&mut transcript).unwrap();


        // let elapsed_time = nowOpens.elapsed();
        // println!("KZG: Time to do openings for KZG is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);

        let elapsed_time = now.elapsed();
        println!("Time to do WHOLE PROVER TIME is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);


    //     //-----------------------------------------------------------------------------------START OF VERIFIER WORK:-------------------------------------------------------------------------------
    //     // //Verify hash pre-image   
        let now = Instant::now();
        PCS::batch_verify(&ver_param,&evalComs,&evalPoints,&openProofs,&mut transcriptVerifier).unwrap();
        PCS::batch_verify(&ver_param,&evalComsBig,&evalPointsBig,&openProofsBig,&mut transcriptVerifier).unwrap();

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

fn main(){
    let args: Vec<String> = env::args().collect();

    let first_size = args[1].parse::<usize>().unwrap();
    let mut last_size = first_size;
    if args.len() == 3{
        last_size = args[2].parse::<usize>().unwrap();
    }

    for i in first_size..last_size+1 {
        println!("Three Channel Grayscale, HyperVerITAS KZG. Size: 2^{:?}\n", i);
        let _res = run_three_channel_gray(i);
        println!("-----------------------------------------------------------------------");
    }
}