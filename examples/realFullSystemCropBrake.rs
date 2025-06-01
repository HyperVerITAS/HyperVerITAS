// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.

#![allow(warnings)]

use core::num;
use std::{ops::Deref, primitive, str::FromStr, time::Instant};

use ark_std::{
    end_timer,
    rand::{self, RngCore},
    start_timer,
};
use proc_status::ProcStatus;
use std::{marker::PhantomData};

use arithmetic::bit_decompose;
use ark_std::{rand::RngCore as R, test_rng};
use itertools::Itertools;
mod helper;
use helper::*;
mod image;
use image::*;
mod protocols;
use protocols::*;
// mod prover;
// use prover::*;
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;
mod brakedownIOP;
use brakedownIOP::*;
use std::env;

use plonkish_backend::{
    halo2_curves::{bn256::{Bn256, Fr}, ff::BatchInverter},
    pcs::{
        multilinear::{MultilinearBrakedown, MultilinearBrakedownCommitment, ZeromorphFri },
        univariate::{Fri, FriProverParams, FriVerifierParams},
        Evaluation, // multilinear::MultilinearPolynomial
        PolynomialCommitmentScheme as _,
    },
    piop::sum_check::{classic::{ClassicSumCheck, ClassicSumCheckProver,EvaluationsProver}, evaluate, SumCheck, VirtualPolynomial},
    poly::{self, multilinear::{rotation_eval,MultilinearPolynomial}, Polynomial},
    util::{
        arithmetic::{BatchInvert, BooleanHypercube, Field as myField}, code::{Brakedown, BrakedownSpec6}, expression::{CommonPolynomial, Expression, Query, Rotation}, goldilocksMont::GoldilocksMont as F, hash::Blake2s, transcript::{
            FieldTranscriptWrite, InMemoryTranscript, Keccak256Transcript, TranscriptWrite
        }
    },
};

type Pcs = MultilinearBrakedown<F, Blake2s, BrakedownSpec6>;

const irredPolyTable: &[u32] = &[
    0, 0, 7, 11, 19, 37, 67, 131, 285, 529, 1033, 2053, 4179, 8219, 16707, 32771, 69643, 131081,
    262273, 524327, 1048585, 2097157, 4194307, 8388641, 16777351, 33554441, 67108935,
];


//For nv = 15, we should do polyforT 32771 with corresponding 69643
//For nv = 10, we should do polyforT 1033 with corresponding 2053
//For nv = 11, we should do polyforT 2053 with corresp 4179
//We just now add
//13 corresp 8219
//14 corresp 16707
// 9 corresp 529
//8 corresp 285
//We pad with 0s for deg 0 and deg 1, as no prim poly for those...

fn hashPreimageProve(
    pp: <MultilinearBrakedown<F, Blake2s, BrakedownSpec6> as plonkish_backend::pcs::PolynomialCommitmentScheme<F>>::ProverParam,
    numCols: usize,
    numRows: usize,
    RGBEvals: [Vec<F>;3],
    RBGEvalsInt: [Vec<usize>;3],
    transcript: &mut (impl TranscriptWrite<<MultilinearBrakedown<F, Blake2s, BrakedownSpec6> as plonkish_backend::pcs::PolynomialCommitmentScheme<F>>::CommitmentChunk, F> + InMemoryTranscript),
) -> (
    Vec<MultilinearBrakedownCommitment<F, Blake2s>>,
    Vec<MultilinearPolynomial<F>>,
    [Vec<F>;1],
    Vec<MultilinearBrakedownCommitment<F, Blake2s>>,
    Vec<MultilinearPolynomial<F>>,
    Vec<Vec<F>>,
){
    //We assume we use the randomness matrix.
    let mut rng = test_rng();

    let mut matrixA = Vec::new();
    for i in 0..128 {
        matrixA.push(ChaCha8Rng::seed_from_u64(i));
    }
    //We are given the image polynomial
    
    let mut imgPolies: Vec<MultilinearPolynomial<F>> = Vec::new();

    imgPolies.push(MultilinearPolynomial::<F>::new(RGBEvals[0].clone()));
    imgPolies.push(MultilinearPolynomial::<F>::new(RGBEvals[1].clone()));
    imgPolies.push(MultilinearPolynomial::<F>::new(RGBEvals[2].clone()));

    let now = Instant::now();
    let imgComs = Pcs::batch_commit_and_write(&pp, &imgPolies, transcript);

    //We make Frievald random vec
    let frievaldRandVec = transcript.squeeze_challenges(1 << numRows);

    //We make rT*A --------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    let now = Instant::now();

    let mut rTA = Vec::new();

    for i in 0..(1 << numCols) {
        let mut mySum = F::ZERO;
        for j in 0..128 {
            mySum += F::random(&mut matrixA[j]) * frievaldRandVec[j];
        }
        rTA.push(mySum);
    }

    let rTAPoly = MultilinearPolynomial::<F>::new(rTA.clone());
    let elapsed_time = now.elapsed();
    println!(
        "Prover time to do rTA is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );

    //We run the sumcheck on rTA * I------------------------------------------------------------------------------------------------------------------------------------------------------------

    let poly_0 = Expression::<F>::Polynomial(Query::new(0, Rotation::cur()));
    let poly_1 = Expression::<F>::Polynomial(Query::new(1, Rotation::cur()));
    let poly_2 = Expression::<F>::Polynomial(Query::new(2, Rotation::cur()));
    let poly_3 = Expression::<F>::Polynomial(Query::new(3, Rotation::cur()));

    let alpha_1 = transcript.squeeze_challenge();
    let alpha_2 = transcript.squeeze_challenge();

    let prod = poly_0.clone()  * poly_1 + 
                                                           Expression::Constant(alpha_1) * poly_0.clone() * poly_2 + 
                                                           Expression::Constant(alpha_2) * poly_0.clone() * poly_3;

    let polys = vec![rTAPoly.clone(), imgPolies[0].clone(), imgPolies[1].clone(), imgPolies[2].clone()];

    let challenges = vec![transcript.squeeze_challenge()];
    let rand_vector = transcript.squeeze_challenges(numCols);
    let ys = [rand_vector.clone()];

    let mut my_sum_0 = F::ZERO;
    let mut my_sum_1 = F::ZERO;
    let mut my_sum_2 = F::ZERO;

    let rta_evals = rTAPoly.evals();
    let img0_evals = imgPolies[0].evals();
    let img1_evals = imgPolies[1].evals();
    let img2_evals = imgPolies[2].evals();
    for i in (0..rta_evals.len()){
        my_sum_0 += rta_evals[i] * img0_evals[i];
        my_sum_1 += rta_evals[i] * img1_evals[i];
        my_sum_2 += rta_evals[i] * img2_evals[i];
    }

    let my_sum: F = my_sum_0 + alpha_1 * my_sum_1 + alpha_2 * my_sum_2;

    let proof_mm = {
        <ClassicSumCheck<EvaluationsProver<F>>>::prove(&(), numCols, VirtualPolynomial::new(&prod, &polys, &challenges, &ys), my_sum, transcript).unwrap();
    };

    let elapsed_time = now.elapsed();
    println!(
        "Prover time to do Sumcheck for hash preimage is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    let mut mySum = F::ZERO;

    //We run range check on image-----------------------------------------------------------------------------------------------------------------------------------------------------------------------
    let now = Instant::now();
    
    let (mut exp_outs, mut poly_outs, mut chall_outs, mut ys_outs, mut com_outs) = (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for i in 0..3{
        let mut hTable = vec![0; 257];
        for j in 0..RBGEvalsInt[0].len(){
            hTable[RBGEvalsInt[i][j]] += 1;
        }
        let (mut exp_out, mut poly_out, mut chall_out, mut ys_out, mut com_out)= range_checkProverIOP(
            pp.clone(),
            numCols,
            255.try_into().unwrap(),
            hTable,
            imgPolies[i].clone(),
            irredPolyTable[numCols].try_into().unwrap(),
            irredPolyTable[numCols+1].try_into().unwrap(),
            transcript,
            0,
        );

        let proof_range = {
            <ClassicSumCheck<EvaluationsProver<F>>>::prove(&(), numCols+1, VirtualPolynomial::new(&exp_out.clone(), &poly_out.clone(), &chall_out.clone(), &[ys_out.clone()]), F::ZERO, transcript).unwrap();
        };
        exp_outs.push(exp_out);
        poly_outs.append(&mut poly_out);
        chall_outs.append(&mut chall_out);
        ys_outs.push(ys_out);
        com_outs.append(&mut com_out);
    }

    // let alpha_3 = transcript.squeeze_challenge();
    // let alpha_4 = transcript.squeeze_challenge();

    // let range_exp = exp_outs[0].clone();

    // //let range_exp = exp_outs[0].clone() + Expression::Constant(alpha_3) * exp_outs[1].clone() + Expression::Constant(alpha_4) * exp_outs[2].clone();
    

    let elapsed_time = now.elapsed();
    println!(
        "Prover time to do MultCheck for hash preimage is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );

    return (imgComs.unwrap(), imgPolies, ys, com_outs, poly_outs, ys_outs);
}

pub fn matSparseMultVec(
    numRows: usize,
    numCols: usize,
    sprseRep: &[Vec<(usize, F)>],
    r: &[F],
) -> Vec<F> {
    let mut Ar = Vec::new();
    for i in 0..numRows {
        let mut mySum = F::ZERO;
        for j in 0..sprseRep[i].len() {
            mySum += sprseRep[i][j].1 * r[sprseRep[i][j].0];
        }
        // println!("THIS IS MYSUM {}", mySum);
        Ar.push(mySum);
    }
    return Ar;
}

pub fn cropProveAffineIOP_real(
    pp: <MultilinearBrakedown<F, Blake2s, BrakedownSpec6> as plonkish_backend::pcs::PolynomialCommitmentScheme<F>>::ProverParam,
    nvOrig: usize,
    nvCrop: usize,
    origImgR: MultilinearPolynomial<F>,
    origImgG: MultilinearPolynomial<F>,
    origImgB: MultilinearPolynomial<F>,
    croppedImgR: MultilinearPolynomial<F>,
    croppedImgG: MultilinearPolynomial<F>,
    croppedImgB: MultilinearPolynomial<F>,
    origWidth: usize,
    origHeight: usize,
    startX: usize,
    startY: usize,
    endX: usize,
    endY: usize,
    transcript: &mut (impl TranscriptWrite<<MultilinearBrakedown<F, Blake2s, BrakedownSpec6> as plonkish_backend::pcs::PolynomialCommitmentScheme<F>>::CommitmentChunk, F> + InMemoryTranscript),
) -> (Vec<MultilinearPolynomial<F>>, [Vec<F>; 1])
{
    let mut rng = test_rng();
    let width = endX - startX;
    let height = endY - startY;
    //create permutation
    let mut cropPerm = Vec::new();
    // println!("Made it 1");

    for i in 0..1 << nvOrig {
        let mut row = Vec::new();

        cropPerm.push(row);
    }
    let mut counter = 0;
    let mut initVal = origWidth * (startY) + (startX);
    for i in 0..(height) {
        for j in 0..(width) {
            cropPerm[initVal].push((counter, F::ONE));
            counter += 1;
            initVal += 1;
        }
        initVal += origWidth - (width + 1);
    }

    // MAKE THIS COME FROM TRANSCRIPT
    let mut frievaldRandVec = transcript.squeeze_challenges(1<<nvCrop);
    let frievaldRand = MultilinearPolynomial::new(frievaldRandVec.clone());

    // println!("{:?}", frievaldRandVec);
    // println!("{:?}", 1<<nvCrop);

    let now = Instant::now();
    let permTimesR = matSparseMultVec(1 << nvOrig, 1 << nvCrop, &cropPerm, &frievaldRandVec);
    let elapsed_timeProver = now.elapsed();
    println!(
        "Verifier/Prover time in PermTimesR is {} seconds.",
        elapsed_timeProver.as_millis() as f64 / 1000 as f64
    );

    // println!("Made it 2.5");
    let now = Instant::now();

    let permTimesRPoly = MultilinearPolynomial::new(permTimesR.clone());

    let elapsed_timeProver = now.elapsed();
    println!(
        "Time to turn perm times R into poly {} seconds.",
        elapsed_timeProver.as_millis() as f64 / 1000 as f64
    );

    // let now = Instant::now();
    // // let myRand = Arc::new(DenseMultilinearExtension::rand(nvOrig, &mut rng));
    // // let mut myRand = &myRand.evaluations;
    // // permTimesRPoly.evaluate(&myRand).unwrap();
    // let elapsed_timeProver = now.elapsed();
    // println!(
    //     "Time to evaluate polynomial is {} SECONDS.-------------------------------------------------------------------------------",
    //     elapsed_timeProver.as_millis() as f64 / 1000 as f64
    // );

    let mut perm_r_poly = Expression::<F>::Polynomial(Query::new(0, Rotation::cur()));
    let mut perm_g_poly = Expression::<F>::Polynomial(Query::new(1, Rotation::cur()));
    let mut perm_b_poly = Expression::<F>::Polynomial(Query::new(2, Rotation::cur()));

    let mut perm_poly = Expression::<F>::Polynomial(Query::new(3, Rotation::cur()));

    let polies = vec![origImgR.clone(), origImgG.clone(), origImgB.clone(), permTimesRPoly.clone()];

    let mut IPermR = perm_poly.clone() * perm_r_poly;
    let mut IPermG = perm_poly.clone()  * perm_g_poly;
    let mut IPermB = perm_poly.clone()  * perm_b_poly;

    // let mut mySum2 = F::zero();
    // for i in 0..1<<nvOrig{
    //     mySum2 += permTimesR[i] * origImgR.evaluations[i];
    // }
    // println!("{}", mySum2);
    // println!("Made it 3");
    let alpha_1 = transcript.squeeze_challenge();
    let alpha_2 = transcript.squeeze_challenge();

    let juicer = IPermR + Expression::Constant(alpha_1) * IPermG + Expression::Constant(alpha_2) * IPermB;

    let challenges = vec![transcript.squeeze_challenge()];
    let rand_vector = transcript.squeeze_challenges(nvOrig);

    let ys = [rand_vector.clone()];

    let mut my_sum = F::ZERO;
    for i in 0..1 << nvOrig {
        my_sum += (polies[0].evals()[i] + polies[1].evals()[i]*alpha_1 + polies[2].evals()[i]*alpha_2) * polies[3].evals()[i];
    }

    //let now = Instant::now();
    let proof_range = {
        <ClassicSumCheck<EvaluationsProver<F>>>::prove(&(), nvOrig, VirtualPolynomial::new(&juicer.clone(), &polies.clone(), &challenges.clone(), &ys.clone()), my_sum, transcript).unwrap();
    };
    // let elapsed_timeProver = now.elapsed();
    // println!(
    //     "Time to run sumcheck IOP is {} seconds.",
    //     elapsed_timeProver.as_millis() as f64 / 1000 as f64
    // );

    // return polies, ys and then open stuff ig
    // in the eval loop, after the loop, add one more point to the points vector, one more point to evals
    // open the image on the random thing (ys) for all three channels.
    return (polies.clone(), ys.clone())
   

}



fn run_whole_system_crop_brake(testSize: usize) {
    let mut rng = test_rng();
    // let numCols = ((testSize * 1000) as f64).log2().ceil() as usize;
    let numCols = testSize;

    // let numCols = 17;

    let cropNumRows = testSize-1;
    let numRows = 7;
    let length = numCols + 1;
    

    // FRI SETUP----------------------------------------------------------------------------------------------------------
    let (pp, vp) = {
        let poly_size = 1 << length;
        let param = Pcs::setup(poly_size, 1, &mut rng).unwrap();
        Pcs::trim(&param, poly_size, 4).unwrap()
    };

    let mut transcriptFri = Keccak256Transcript::new(());

    let fileName = format!("test/Timings{}.json", testSize);


    for iii in 0..1 {
        // LOAD IMAGE----------------------------------------------------------------------------------------------------------
        let origImg = load_image(&fileName);
        println!("this is dim {:?}", origImg.cols * origImg.rows);
        //Below we do padding, prover works with padded image, but later sends the unpadded commitment to verifier (this is fine as unpadded effectively has padding as 0)
        let mut RGBEvalsFri =
            [toFieldVecFri::<F>(&origImg.R.iter().map(|&x| x as u64).collect::<Vec<_>>()),
            toFieldVecFri::<F>(&origImg.G.iter().map(|&x| x as u64).collect::<Vec<_>>()),
            toFieldVecFri::<F>(&origImg.B.iter().map(|&x| x as u64).collect::<Vec<_>>()),
            ];

        //We implement padding
        // for i in 0..(RGBEvalsFri[0].len().next_power_of_two() - RGBEvalsFri[0].len()) {
        

        // for i in 0..( RGBEvalsFri[0].len()) {

        //     RGBEvalsFri[0].push(F::ZERO);
        //     RGBEvalsFri[1].push(F::ZERO);
        //     RGBEvalsFri[2].push(F::ZERO);

        // }
        println!("THIS IS LEN {}",RGBEvalsFri[0].len());
        //THIS IS HASHING MATRIX CREATED BY CAMERA------------------------------------------------------------
        let mut testDigestRGB = Vec::new();
        for k in 0..3{
            let mut matrixA = Vec::new();
            for i in 0..128 {
                matrixA.push(ChaCha8Rng::seed_from_u64(i));
            }
            //THIS IS HASHING DONE BY CAMERA------------------------------------------------------------
            let mut testDigest = Vec::new();
            for i in 0..128 {
                let mut mySum = F::ZERO;
                for j in 0..(1 << numCols) {
                    //mySum +=  RGBEvalsFri[k][j];
                    // PLACEHOLDER UNTIL I FIGURE OUT RANDOMNESS
                    mySum += F::random(&mut matrixA[i]) * RGBEvalsFri[k][j];
                }
                testDigest.push(mySum);
            }
            testDigestRGB.push(testDigest);
        }

        //THIS IS PROVER DOING EVERYTHING
        // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT IMG--------------------------------------------------------------------------------------------------------------------------
        let now = Instant::now();
        let origImg = load_image(&fileName);

        let mut allFriTimes = 0.0;

        // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT END--------------------------------------------------------------------------------------------------------------------------

        let mut r_chan: Vec<usize> = origImg.R.iter().map(|x| (*x).into()).collect();
        let mut g_chan: Vec<usize> = origImg.R.iter().map(|x| (*x).into()).collect();
        let mut b_chan: Vec<usize> = origImg.R.iter().map(|x| (*x).into()).collect();

        // NOTE: only works for images of size 2^n
        // let a: usize = 0;
        // r_chan.append(&mut vec![a; r_chan.len()]);
        // b_chan.append(&mut vec![a; b_chan.len()]);
        // g_chan.append(&mut vec![a; g_chan.len()]);


        // TIME THE IOP------------------------------------------------------------------------------------
        //let now: Instant = Instant::now();
        let (imgComs, imgPolies,imgYs, com_outs, poly_outs, ys_outs) =
            hashPreimageProve(
                pp.clone(),
                numCols,
                numRows,
                RGBEvalsFri,
                [r_chan, g_chan, b_chan],
                &mut transcriptFri,
            );
        // let elapsed_time = now.elapsed();
        // println!(
        //     "Prover time to do IOP is {:?} seconds",
        //     elapsed_time.as_millis() as f64 / 1000 as f64
        // );
        // //-----------------------------------------------------------------------------------CROPPING--------------------------------------------------------------------------------------------
        //let now: Instant = Instant::now();
        // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT H--------------------------------------------------------------------------------------------------------------------------
        //let nowOpens = Instant::now();

        let mut friPolies = Vec::new();
        //let mut friPolyVectors = Vec::new();
        for i in 0..3{
            let mut padded = imgPolies[i].clone().evals().to_vec();
            padded.append(&mut vec![F::ZERO; 1<< numCols]);
            friPolies.push(MultilinearPolynomial::new(padded));
        }
        for i in 0..3{
            friPolies.push(poly_outs[7*i+6].clone());
            friPolies.push(poly_outs[7*i].clone());
            friPolies.push(poly_outs[7*i+1].clone());
        }

        let mut friPolyComs = imgComs.clone();
        for i in 0..3{
            friPolyComs.push(com_outs[3*i+2].clone());
            friPolyComs.push(com_outs[3*i].clone());
            friPolyComs.push(com_outs[3*i+1].clone());
        }

        // let elapsed_time = nowOpens.elapsed();
        // println!("FRI: Time to do COMMITMENTS FOR h, prod, frac, for FRI is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
        // allFriTimes += elapsed_time.as_millis() as f64 / 1000 as f64;

        // // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT END--------------------------------------------------------------------------------------------------------------------------
        
        let cropFileName = format!("test/Crop{}.json", testSize);

        let cropImg = load_image(cropFileName);

        let origImgRPoly = MultilinearPolynomial::new(toFieldVecFri::<F>(&origImg.R.iter().map(|&x| x as u64).collect::<Vec<_>>()));
        let origImgGPoly = MultilinearPolynomial::new(toFieldVecFri::<F>(&origImg.G.iter().map(|&x| x as u64).collect::<Vec<_>>()));
        let origImgBPoly = MultilinearPolynomial::new(toFieldVecFri::<F>(&origImg.B.iter().map(|&x| x as u64).collect::<Vec<_>>()));

        let cropImgPolyR  = MultilinearPolynomial::new(toFieldVecFri::<F>(&cropImg.R.iter().map(|&x| x as u64).collect::<Vec<_>>()));
        let cropImgPolyG  = MultilinearPolynomial::new(toFieldVecFri::<F>(&cropImg.G.iter().map(|&x| x as u64).collect::<Vec<_>>()));
        let cropImgPolyB  = MultilinearPolynomial::new(toFieldVecFri::<F>(&cropImg.B.iter().map(|&x| x as u64).collect::<Vec<_>>()));

        // origImg.cols * origImg.rows
        let (cropStartX,cropStartY) = (0,0);
        let (crop_polys, ys_crop) = cropProveAffineIOP_real(pp.clone(), numCols,cropNumRows, origImgRPoly.clone(), origImgGPoly.clone(),origImgBPoly.clone(), cropImgPolyR, cropImgPolyG, cropImgPolyB, origImg.cols, origImg.rows,
            cropStartX,cropStartY, cropStartX+numCols, cropStartY+numRows, &mut transcriptFri);
        // // --------------------------------------------------------------------------------------------------------------------------FRI OPENINGS--------------------------------------------------------------------------------------------------------------------------
        //let nowOpens = Instant::now();

        // //We now do some ridiculous openings (13)
        // //WE GET POINTS.
        //let nowOpens = Instant::now();
        let mut polynomials = friPolies;
        let mut coms = friPolyComs;
        let mut points = Vec::new();
        let mut evals = Vec::new();
        // ----------------------------------------------START OF MAKING EVAL POINTS----------------------------------------------

        let mut origPt: Vec<F> = imgYs[0].clone();
        origPt.push(F::ZERO);
        points.push(origPt.clone());
        
        // 0 vector, used for h
        let mut pt0: Vec<F> = vec![F::ZERO; numCols];
        pt0.push(F::ZERO);
        points.push(pt0.clone());
        // 1..10 vector, used for prod 
        let mut final_query = vec![F::ONE; numCols+1];
        final_query[0] = F::ZERO;
        points.push(final_query);
        // Eval for range for image
        for i in 0..3{

            let mut myRandSmall = ys_outs[i].clone();
            // for k in 0..ys_outs[i].len()-1{
            //     myRandSmall.push(ys_outs[i][k]);
            // }
            points.push(myRandSmall.clone());

            // DEBUGGUGUGGG Galois reps
            // point 1 for h_{+1}
            myRandSmall[2] = F::ONE - myRandSmall[2];
            points.push(myRandSmall.clone());
            // point 2 for h_{+1}
            myRandSmall[2] = F::ONE - myRandSmall[3];
            points.push(myRandSmall.clone());

            //Rand point used for prod and frac polies 
            let mut myRand = ys_outs[i].clone();
            points.push(myRand.clone());
        
            // Randpoint but last is 0
            myRand[numCols] = F::ZERO;
            points.push(myRand.clone());
            // Randpoint but last is 1
            myRand[numCols] = F::ONE;
            points.push(myRand.clone());    
        }
        // zero can be at beginning or end depending on little endian or big endian
        let mut little_juicer = ys_crop[0].clone();
        little_juicer.push(F::ZERO);
        points.push(little_juicer.clone());
        // ----------------------------------------------END OF MAKING EVAL POINTS----------------------------------------------
        for i in 0..3{
        // //----------------------------------------------We first add opening for matrixMult for hash.----------------------------------------------    
            evals.push(Evaluation::new(
                0,
                0,
                polynomials[0].evaluate(&points[0]),
            ));

            // //----------------------------------------------We now add 0 for h----------------------------------------------
            // println!("{}",3+ i* 3);
            evals.push(Evaluation::new(
                3+ i* 3, //This is the poly index
                1, //This is the point index
                polynomials[3+ i* 3].evaluate(&points[1]),
            ));

            // // //----------------------------------------------We now add alpha_range for image----------------------------------------------
            evals.push(Evaluation::new(
                i, //This is the poly index
                3 + i*6, //This is the point index
                polynomials[i].evaluate(&points[3 + i*6]),
            ));
            // // //----------------------------------------------We now add alpha_range for h----------------------------------------------
            evals.push(Evaluation::new(
                3+i*3, //This is the poly index
                3 + i*6, //This is the point index
                polynomials[3+i*3].evaluate(&points[3 + i*6]),
            ));
        
            // // //----------------------------------------------We now add alpha_range modified0 for h----------------------------------------------
            evals.push(Evaluation::new(
                3+i*3, //This is the poly index
                4 + i*6, //This is the point index
                polynomials[3+i*3].evaluate(&points[4 + i*6]),
            ));

            // // //----------------------------------------------We now add alpha_range modified1 for h----------------------------------------------
            evals.push(Evaluation::new(
                3+i*3, //This is the poly index
                5 + i*6, //This is the point index
                polynomials[3+i*3].evaluate(&points[5 + i*6]),
            ));
            
            // // //WE NOW DO BIG POLYNOMIALS --------------------------------------------------------------------------------------------
            // // //----------------------------------------------We then add prod for 1...10----------------------------------------------
            evals.push(Evaluation::new(
                5+i*3, //This is the poly index
                2, //This is the point index
                polynomials[5+i*3].evaluate(&points[2]),
            ));
        
            // // //----------------------------------------------We now add alpha_range for prod----------------------------------------------
            evals.push(Evaluation::new(
                5+i*3, //This is the poly index
                6+i*6, //This is the point index
                polynomials[5+i*3].evaluate(&points[6+i*6]),
            ));

            // // //----------------------------------------------We now add alpha_range for frac----------------------------------------------
   
            evals.push(Evaluation::new(
                4+i*3, //This is the poly index
                6+i*6, //This is the point index
                polynomials[4+i*3].evaluate(&points[6+i*6]),
            ));
            // //----------------------------------------------we now add alpha_range||0 for prod----------------------------------------------

            evals.push(Evaluation::new(
                4+i*3, //This is the poly index
                7+i*6, //This is the point index
                polynomials[4+i*3].evaluate(&points[7+i*6]),
            ));

            // // // // //----------------------------------------------we now add alpha_range||0 for frac----------------------------------------------
            evals.push(Evaluation::new(
                5+i*3, //This is the poly index
                7+i*6, //This is the point index
                polynomials[5+i*3].evaluate(&points[7+i*6]),
            ));            

            // // // //----------------------------------------------we now add alpha_range||1 for prod----------------------------------------------
   
            evals.push(Evaluation::new(
                4+i*3, //This is the poly index
                8+i*6, //This is the point index
                polynomials[4+i*3].evaluate(&points[8+i*6]),
            ));

            // // // //----------------------------------------------we now add alpha_range||1 for frac----------------------------------------------
            evals.push(Evaluation::new(
                5+i*3, //This is the poly index
                8+i*6, //This is the point index
                polynomials[5+i*3].evaluate(&points[8+i*6]),
            ));
            // // // //----------------------------------------------we now add transPoint for IMG ----------------------------------------------
            evals.push(Evaluation::new(
                i, //This is the poly index
                21, //This is the point index
                polynomials[i].evaluate(&points[21]),
            ));
        }


        println!("MADE IT TO little openings");

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

        // let elapsed_time = nowOpens.elapsed();
        // println!("FRI: Time to do openings for FRI is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
        // allFriTimes += elapsed_time.as_millis() as f64 / 1000 as f64;
        // println!("FRI: Total FRI time is {:?} seconds",allFriTimes);

        let elapsed_time = now.elapsed();
        println!("Time to do WHOLE PROVER TIME is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);

    //     // --------------------------------------------------------------------------------------------------------------------------END OF FRI OPENINGS--------------------------------------------------------------------------------------------------------------------------

    //     //-----------------------------------------------------------------------------------START OF VERIFIER WORK:-------------------------------------------------------------------------------
    //      
//     let now = Instant::now();
//     // let mut transcriptFri = Keccak256Transcript::new(());
// // 
//     Pcs::batch_verify(
//         &vp,
//         &coms,
//         &points,
//         &evals,
//         &mut transcriptFri,
//     ).unwrap();     
//     let elapsed_time = now.elapsed();
//     println!("FRI: Time to do VERIFY IS {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
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
        println!("Full System Crop, HyperVerITAS Brakedown. Size: 2^{:?}\n", i);
        let _res = run_whole_system_crop_brake(i);
        println!("-----------------------------------------------------------------------");
    }
}