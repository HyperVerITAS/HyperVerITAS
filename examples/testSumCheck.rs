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
    for i in 0..3{
        RHS_RGB.push(VirtualPolynomial::new_from_mle(&rTAPoly, F::one()));
        RHS_RGB[i].mul_by_mle(imgPolies[i].clone(), F::one());
    }
    // RHS_RGB.mul_by_mle(imgPoly.clone(), F::one());

    // WE CAN BATCH THIS...
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

fn main() {
    let testSize = 14;

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
        println!("MADE IT");

   

    let mut transcriptFri = Keccak256Transcript::new(());


    // println!("Test successful");
    let fileName = format!("../test/Timings{}.json", testSize);
    println!(fileName);
    // let srs = PCS::gen_srs_for_testing(&mut rng, length).unwrap();
    // let (pcs_param, ver_param) = PCS::trim(&srs, None, Some(length)).unwrap();
    // for iii in 0..1 {
    //     // LOAD IMAGE----------------------------------------------------------------------------------------------------------
    //     let origImg = load_image(&fileName);
    //     println!("this is dim {:?}", origImg.cols * origImg.rows);
    //     //Below we do padding, prover works with padded image, but later lssends the unpadded commitment to verifier (this is fine as unpadded effectively has padding as 0)
    //     let mut RGBEvals = [toFieldVec(&origImg.R),toFieldVec(&origImg.G),toFieldVec(&origImg.B)];
    //     let mut RGBEvalsFri =
    //         [toFieldVecFri::<FriFR>(&origImg.R.iter().map(|&x| x as u64).collect::<Vec<_>>()),
    //         toFieldVecFri::<FriFR>(&origImg.G.iter().map(|&x| x as u64).collect::<Vec<_>>()),
    //         toFieldVecFri::<FriFR>(&origImg.B.iter().map(|&x| x as u64).collect::<Vec<_>>()),
    //         ];

    //     //We implement padding
    //     // for i in 0..(RGBEvalsFri[0].len().next_power_of_two() - RGBEvalsFri[0].len()) {
        

    //     for i in 0..( RGBEvalsFri[0].len()) {

    //         RGBEvalsFri[0].push(FriFR::ZERO);
    //         RGBEvalsFri[1].push(FriFR::ZERO);
    //         RGBEvalsFri[2].push(FriFR::ZERO);

    //     }
    //     println!("THIS IS LEN {}",RGBEvalsFri[0].len());
    //     //THIS IS HASHING MATRIX CREATED BY CAMERA------------------------------------------------------------
       
    //     //THIS IS PROVER DOING EVERYTHING
    //     let now0 = Instant::now();
    //     let origImg = load_image(&fileName);
    //     let imgPoly = vec_to_poly(toFieldVec(&origImg.R)).0;
    //     let now2 = Instant::now();

    //     let img_comR = PCS::commit(pcs_param.clone(), &imgPoly).unwrap();
    //     let elapsed_time = now2.elapsed();
    //     println!("KZG COMMIT TIME IS {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
    //     // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT IMG--------------------------------------------------------------------------------------------------------------------------
    //     let nowOpens = Instant::now();


    //     let imgPoliesFri: Vec<MultilinearPolynomial<FriFR>> = RGBEvalsFri.iter()
    //         .map(|x| MultilinearPolynomial::<FriFR>::from_evals(x.clone()))
    //         .collect();

    //     let imgPolyFriCom = Pcs::commit_and_write(&pp, &imgPoliesFri, &mut transcriptFri).unwrap();

    //     let elapsed_time = nowOpens.elapsed();
    //     println!("FRI: Time to do COMMIT FOR IMAGE is {:?} seconds", elapsed_time.as_millis() as f64 / 1000 as f64);
    //     // --------------------------------------------------------------------------------------------------------------------------FRI COMMITMENT END--------------------------------------------------------------------------------------------------------------------------

  
    //     // for i in 0..3{
    //     //-----------------------------------------------------------------------------------GRAYSCALING--------------------------------------------------------------------------------------------
        
        
    // }
}
