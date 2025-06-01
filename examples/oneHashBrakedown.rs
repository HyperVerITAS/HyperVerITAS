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

fn hashPreimageOneIOP<F: PrimeField, E, PCS>(
    numCols: usize,
    numRows: usize,
    REvals: Vec<F>,
    transcript: &mut IOPTranscript<E::ScalarField>,
    pcs_param: &PCS::ProverParam,
    ver_param: &PCS::VerifierParam,
) -> (
    [<PolyIOP<F> as SumCheck<F>>::SumCheckProof;1],
    [VPAuxInfo<F>;1],
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

    imgPolies.push(vec_to_poly::<F>(REvals.clone()).0);
    //We make Frievald random vec
    let alpha = transcript.get_and_append_challenge(b"alpha").unwrap();

    let mut frievaldRandVec = Vec::new();

    for i in 0..(1 << numRows) {
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
    RHS_RGB.push(VirtualPolynomial::new_from_mle(&rTAPoly, F::one()));
    RHS_RGB[0].mul_by_mle(imgPolies[0].clone(), F::one());
    
    // RHS_RGB.mul_by_mle(imgPoly.clone(), F::one());

    // WE CAN BATCH THIS...
    let proofRGB = [<PolyIOP<F> as SumCheck<F>>::prove(&RHS_RGB[0], transcript).unwrap()];
    
    let poly_infoRGB = [RHS_RGB[0].aux_info.clone()];
    
    let elapsed_time = now.elapsed();
    println!(
        "Prover time to do Sumcheck for hash preimage is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    let mut mySum = F::zero();

    //We run range check on image-----------------------------------------------------------------------------------------------------------------------------------------------------------------------
    let now = Instant::now();
    let (mut multsetProofRGB, mut fxRGB, mut gxRGB, mut hRGB) = (Vec::new(),Vec::new(),Vec::new(),Vec::new());

    let (multsetProof, fx, gx, h) = range_checkProverIOP::<F, E, PCS>(
    numCols,
    255.try_into().unwrap(),
    imgPolies[0].clone(),
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
    
    let elapsed_time = now.elapsed();
    println!(
        "Prover time to do MultCheck for hash preimage is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );

    //We return a vector containing the final points to evaluate I, the final points to evaulate h(from range check), the final points
    //to evaluate the prod and frac polynomials, as well as the sumcheck proof, range check proof.
    return (proofRGB, poly_infoRGB, multsetProofRGB, fxRGB, gxRGB, hRGB);
}

fn run_one_hash_brake(testSize: usize) {

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

    let chan = "R";
    // println!("Test successful");
    let srs = PCS::gen_srs_for_testing(&mut rng, length).unwrap();
    let (pcs_param, ver_param) = PCS::trim(&srs, None, Some(length)).unwrap();
    for iii in 0..1 {
        // LOAD IMAGE----------------------------------------------------------------------------------------------------------
        let file = read_photo("Veri", chan, &testSize);
        let mut origImg = Vec::<u8>::new();
        for line in file.lines() {
            let line = line.expect("Unable to read line");
            let i = line.parse::<u8>().unwrap();
            origImg.push(i);
        }
        
        //Below we do padding, prover works with padded image, but later sends the unpadded commitment to verifier (this is fine as unpadded effectively has padding as 0)
        let mut REvals = toFieldVec(&origImg);
        let mut REvalsFri = toFieldVecFri::<FriFR>(&origImg.iter().map(|&x| x as u64).collect::<Vec<_>>());

        //We implement padding
        // for i in 0..(RGBEvalsFri[0].len().next_power_of_two() - RGBEvalsFri[0].len()) {
        

        for i in 0..(REvalsFri.len()) {
            REvalsFri.push(FriFR::ZERO);
        }
        println!("THIS IS LEN {}",REvalsFri.len());
        //THIS IS HASHING MATRIX CREATED BY CAMERA------------------------------------------------------------
        let mut testDigestRGB = Vec::new();
        
        let mut matrixA = Vec::new();
        for i in 0..128 {
            matrixA.push(ChaCha8Rng::seed_from_u64(i));
        }
        //THIS IS HASHING DONE BY CAMERA------------------------------------------------------------
        let mut testDigest = Vec::new();
        for i in 0..128 {
            let mut mySum = FriFR::ZERO;
            for j in 0..(1 << numCols) {
                mySum +=  REvalsFri[j];
                // PLACEHOLDER UNTIL I FIGURE OUT RANDOMNESS
                // mySum += FriFR::rand(&mut matrixA[i]) * RGBEvalsFri[i][j];
            }
            testDigest.push(mySum);
        }
        testDigestRGB.push(testDigest);
    
        //THIS IS PROVER DOING EVERYTHING
        let now: Instant = Instant::now();

        let file = read_photo("Veri", "R", &testSize);
        let mut origImg = Vec::<u8>::new();
        for line in file.lines() {
            let line = line.expect("Unable to read line");
            let i = line.parse::<u8>().unwrap();
            origImg.push(i);
        }
        let imgPoly = vec_to_poly(toFieldVec(&origImg)).0;

        let now2 = Instant::now();
        let img_comR = PCS::commit(pcs_param.clone(), &imgPoly).unwrap();
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
        let (proofRGB, poly_info_matMult, multsetProof, prod_xRGB, frac_xRGB, hRGB) =
            hashPreimageOneIOP::<F, Bls12_381, MultilinearKzgPCS<Bls12_381>>(
                numCols,
                numRows,
                REvals,
                &mut transcript,
                &pcs_param,
                &ver_param,
            );
    
        //-----------------------------------------------------------------------------------CROPPING--------------------------------------------------------------------------------------------

        // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT H--------------------------------------------------------------------------------------------------------------------------

        let mut friPolies = Vec::new();
        let mut friPolyVectors = Vec::new();

        let mut valsH: Vec<FriFR> = hRGB[0].evaluations.iter().map(|x| kzgFieldToFriField(x)).collect();
        // let polyHFri = MultilinearPolynomial::<FriFR>::from_evals(valsH);
        // friPolies.push(&polyHFri);
        for j in 0..1<<numCols{
            valsH.push(FriFR::ZERO);
        }
        let valsProdX: Vec<FriFR> = prod_xRGB[0].evaluations.iter().map(|x| kzgFieldToFriField(x)).collect();

        let valsFracX: Vec<FriFR> = frac_xRGB[0].evaluations.iter().map(|x| kzgFieldToFriField(x)).collect();

        friPolyVectors.push(valsH);
        friPolyVectors.push(valsProdX);
        friPolyVectors.push(valsFracX);

        friPolies = friPolyVectors.iter()
        .map(|x| MultilinearPolynomial::<FriFR>::from_evals(x.clone()))
        .collect();
        let friPolyComs = Pcs::batch_commit(&pp, &friPolies);

        // // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT END--------------------------------------------------------------------------------------------------------------------------
        // // --------------------------------------------------------------------------------------------------------------------------FRI OPENINGS--------------------------------------------------------------------------------------------------------------------------

        let mut polynomials = imgPoliesFri;
        polynomials.append(&mut friPolies);
        let mut coms = imgPolyFriCom;
        coms.append(&mut friPolyComs.unwrap());
        let mut points = Vec::new();
        let mut evals = Vec::new();
        // ----------------------------------------------START OF MAKING EVAL POINTS----------------------------------------------

        let mut origPt: Vec<FriFR> = proofRGB[0].point.iter().map(|x| kzgFieldToFriField(x)).collect();

        origPt.push(FriFR::ZERO);
        points.push(origPt.clone());

        // 0 vector, used for h
        let mut pt0: Vec<FriFR> = vec![F::zero(); numCols].iter().map(|x| kzgFieldToFriField(x)).collect();
        pt0.push(FriFR::ZERO);
        points.push(pt0.clone());
        // 1..10 vector, used for prod 
        let mut final_query = vec![FriFR::ONE; numCols+1];
        final_query[0] = FriFR::ZERO;
        points.push(final_query);
        // Eval for range for image

        let mut myRand = Vec::new();
        for k in 0 .. numCols{
            myRand.push(F::rand(&mut rng));
        }
        let mut myRandSmall = myRand.clone();
        myRand.push(F::rand(&mut rng));
        let mut ptRandSmall: Vec<FriFR> = myRandSmall.iter().map(|x| kzgFieldToFriField(x)).collect();
        myRandSmall.push(F::zero());
        ptRandSmall.push(FriFR::ZERO);
        points.push(ptRandSmall.clone());
        // point 1 for h_{+1}
        ptRandSmall[2] = FriFR::ONE - ptRandSmall[2];
        points.push(ptRandSmall.clone());
        // point 2 for h_{+1}
        ptRandSmall[2] = FriFR::ONE - ptRandSmall[3];
        points.push(ptRandSmall.clone());
        //Rand point used for prod and frac polies 
        let mut ptRand: Vec<FriFR> = myRand.iter().map(|x| kzgFieldToFriField(x)).collect();
        points.push(ptRand.clone());
        // Randpoint but last is 0
        ptRand[numCols] = FriFR::ZERO;
        points.push(ptRand.clone());
        // Randpoint but last is 1
        ptRand[numCols] = FriFR::ONE;
        points.push(ptRand.clone());    
        // ----------------------------------------------END OF MAKING EVAL POINTS----------------------------------------------

        // //----------------------------------------------We first add opening for matrixMult for hash.----------------------------------------------    
        evals.push(Evaluation::new(
            0,
            0,
            polynomials[0].evaluate(&points[0]),
        ));

        // //----------------------------------------------We now add 0 for h----------------------------------------------
        // println!("{}",3+ i* 3);
        evals.push(Evaluation::new(
            1, //This is the poly index
            1, //This is the point index
            polynomials[1].evaluate(&points[1]),
        ));

        // // //----------------------------------------------We now add alpha_range for image----------------------------------------------
        evals.push(Evaluation::new(
            0, //This is the poly index
            3, //This is the point index
            polynomials[0].evaluate(&points[3]),
        ));
        // // //----------------------------------------------We now add alpha_range for h----------------------------------------------
        evals.push(Evaluation::new(
            1, //This is the poly index
            3, //This is the point index
            polynomials[1].evaluate(&points[3]),
        ));
    
        // // //----------------------------------------------We now add alpha_range modified0 for h----------------------------------------------
        evals.push(Evaluation::new(
            1, //This is the poly index
            4, //This is the point index
            polynomials[1].evaluate(&points[4]),
        ));

        // // //----------------------------------------------We now add alpha_range modified1 for h----------------------------------------------
        evals.push(Evaluation::new(
            1, //This is the poly index
            5, //This is the point index
            polynomials[1].evaluate(&points[5]),
        ));
        
        // // //WE NOW DO BIG POLYNOMIALS --------------------------------------------------------------------------------------------
        // // //----------------------------------------------We then add prod for 1...10----------------------------------------------
        evals.push(Evaluation::new(
            2, //This is the poly index
            2, //This is the point index
            polynomials[2].evaluate(&points[2]),
        ));
    
        // // //----------------------------------------------We now add alpha_range for prod----------------------------------------------
        evals.push(Evaluation::new(
            2, //This is the poly index
            6, //This is the point index
            polynomials[2].evaluate(&points[6]),
        ));

        // // //----------------------------------------------We now add alpha_range for frac----------------------------------------------

        evals.push(Evaluation::new(
            3, //This is the poly index
            6, //This is the point index
            polynomials[3].evaluate(&points[6]),
        ));
        // //----------------------------------------------we now add alpha_range||0 for prod----------------------------------------------

        evals.push(Evaluation::new(
            2, //This is the poly index
            7, //This is the point index
            polynomials[2].evaluate(&points[7]),
        ));

        // // // // //----------------------------------------------we now add alpha_range||0 for frac----------------------------------------------
        evals.push(Evaluation::new(
            3, //This is the poly index
            7, //This is the point index
            polynomials[3].evaluate(&points[7]),
        ));            

        // // // //----------------------------------------------we now add alpha_range||1 for prod----------------------------------------------

        evals.push(Evaluation::new(
            2, //This is the poly index
            8, //This is the point index
            polynomials[2].evaluate(&points[8]),
        ));

        // // // //----------------------------------------------we now add alpha_range||1 for frac----------------------------------------------
        evals.push(Evaluation::new(
            3, //This is the poly index
            8, //This is the point index
            polynomials[3].evaluate(&points[8]),
        ));
            // // // //----------------------------------------------we now add transPoint for IMG ----------------------------------------------
        println!("made it to batch openings");

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
        println!("One Channel Hash, HyperVerITAS Brakedown. Size: 2^{:?}\n", i);
        let _res = run_one_hash_brake(i);
        println!("-----------------------------------------------------------------------");
    }
}