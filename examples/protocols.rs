// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.

#![allow(warnings)]

use ark_ec::pairing::Pairing;
use std::{ops::Deref, primitive, str::FromStr, time::Instant};

use ark_bls12_381::{Bls12_381, Fq, Fr, G1Affine, G2Affine};
use ark_ff::{Field, Fp, Fp2, PrimeField, Zero};
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
use std::{marker::PhantomData, sync::Arc};
use transcript::IOPTranscript;

// use ark_test_curves::bls12_381::Fq as F;
use ark_bls12_381::Fr as F;
type PCS = MultilinearKzgPCS<Bls12_381>;
use ark_ff::One;
use ark_std::{rand::RngCore as R, test_rng};
use itertools::Itertools;

use super::helper;

use helper::*;
//For nv = 15, we should do polyforT 32771 with corresponding 69643
//For nv = 10, we should do polyforT 1033 with corresponding 2053
//For nv = 11, we should do polyforT 2053 with corresp 4179
//We just now add
//13 corresp 8219
//14 corresp 16707
// 9 corresp 529
//8 corresp 285
//We pad with 0s for deg 0 and deg 1, as no prim poly for those...
const irredPolyTable: &[u32] = &[
    0, 0, 7, 11, 19, 37, 67, 131, 285, 529, 1033, 2053, 4179, 8219, 16707, 32771, 69643, 131081,
    262273, 524327, 1048585, 2097157, 4194307, 8388641, 16777351, 33554441, 67108935,
];
const flagUseCommits: bool = false;
// const STRINGS: &[&str] = &["str1", "str2"];
//This function takes in a vector representing our image and creates the appropriate polynomial.

//This is grayscale
fn grayscaleCheck<F: PrimeField, E, PCS>(
    R: Arc<DenseMultilinearExtension<F>>,
    G: Arc<DenseMultilinearExtension<F>>,
    B: Arc<DenseMultilinearExtension<F>>,
    Gray: Arc<DenseMultilinearExtension<F>>,
    roundError: Arc<DenseMultilinearExtension<F>>,
    comR: <PCS as PolynomialCommitmentScheme<E>>::Commitment,
    comG: <PCS as PolynomialCommitmentScheme<E>>::Commitment,
    comB: <PCS as PolynomialCommitmentScheme<E>>::Commitment,
    comGray: <PCS as PolynomialCommitmentScheme<E>>::Commitment,
    evalPt: Vec<F>,
    pcs_param: &PCS::ProverParam,
    ver_param: &PCS::VerifierParam,
) -> (u32)
where
    E: Pairing<ScalarField = F>,
    PCS: PolynomialCommitmentScheme<
        E,
        Polynomial = Arc<DenseMultilinearExtension<E::ScalarField>>,
        Point = Vec<F>,
        Evaluation = F,
    >,
{
    //Prover makes opening proofs
    let (openProofR, EvalR) = PCS::open(pcs_param, &R, &evalPt.clone()).unwrap();
    let (openProofG, EvalG) = PCS::open(pcs_param, &G, &evalPt.clone()).unwrap();
    let (openProofB, EvalB) = PCS::open(pcs_param, &B, &evalPt.clone()).unwrap();
    let (openProofGray, EvalGray) = PCS::open(pcs_param, &Gray, &evalPt.clone()).unwrap();

    //Verifier verifies opening proofs
    let verCheckR: bool = PCS::verify(
        &ver_param.clone(),
        &comR.clone(),
        &evalPt.clone(),
        &EvalR.clone(),
        &openProofR.clone(),
    )
    .unwrap();
    let verCheckG = PCS::verify(
        &ver_param.clone(),
        &comG.clone(),
        &evalPt.clone(),
        &EvalG.clone(),
        &openProofG.clone(),
    )
    .unwrap();
    let verCheckB = PCS::verify(
        &ver_param.clone(),
        &comB.clone(),
        &evalPt.clone(),
        &EvalB.clone(),
        &openProofB.clone(),
    )
    .unwrap();
    let verCheckGray = PCS::verify(
        &ver_param.clone(),
        &comGray.clone(),
        &evalPt.clone(),
        &EvalGray.clone(),
        &openProofGray.clone(),
    )
    .unwrap();

    //Verifier checks grayscale relation.
    print!(
        "THIS IS GrayScale Truthiness {:?}\n",
        F::from_le_bytes_mod_order(&[30]) * EvalR
            + F::from_le_bytes_mod_order(&[59]) * EvalG
            + F::from_le_bytes_mod_order(&[11]) * EvalB
            + roundError.evaluate(&evalPt).unwrap()
            == F::from_le_bytes_mod_order(&[100]) * EvalGray
    );
    return 10;
}

pub fn cropProve<F: PrimeField, E, PCS>(
    nv: usize,
    // perm: Vec<F>,
    origImgR: Arc<DenseMultilinearExtension<F>>,
    origImgG: Arc<DenseMultilinearExtension<F>>,
    origImgB: Arc<DenseMultilinearExtension<F>>,
    croppedImgR: Arc<DenseMultilinearExtension<F>>,
    croppedImgG: Arc<DenseMultilinearExtension<F>>,
    croppedImgB: Arc<DenseMultilinearExtension<F>>,
    origWidth: usize,
    origHeight: usize,
    startX: usize,
    startY: usize,
    endX: usize,
    endY: usize,
    pcs_param: &PCS::ProverParam,
    ver_param: &PCS::VerifierParam,
    // point: PCS::Point,
    // myRand: Vec<F>,
    transcript: &mut IOPTranscript<E::ScalarField>,
    transcriptTEST: &mut IOPTranscript<E::ScalarField>,
)
// ->(PolyIOP<F>)
// -> (ProductCheckProof)
where
    E: Pairing<ScalarField = F>,
    PCS: PolynomialCommitmentScheme<
        E,
        Polynomial = Arc<DenseMultilinearExtension<E::ScalarField>>,
        Point = Vec<F>,
        Evaluation = F,
    >,
{
    //We first create the permutated image vector.
    let mut permutedImgR = origImgR.evaluations.clone();
    let mut permutedImgG = origImgG.evaluations.clone();
    let mut permutedImgB = origImgB.evaluations.clone();

    let width = endX - startX;
    let height = endY - startY;
    //create permutation
    let mut perm = Vec::new();
    for i in 0..(origWidth * origHeight) {
        perm.push(F::from_le_bytes_mod_order(&transform_u32_to_array_of_u8(
            i.try_into().unwrap(),
        )));
    }
    for i in 0..(height) {
        for j in 0..(width) {
            // perm[i*width + j ] = F::from_le_bytes_mod_order(&transform_u32_to_array_of_u8((origWidth*(startY+i)+(startX+j)).try_into().unwrap()));
            perm.swap(i * width + j, origWidth * (startY + i) + (startX + j));
            permutedImgR.swap(i * width + j, origWidth * (startY + i) + (startX + j));
            permutedImgG.swap(i * width + j, origWidth * (startY + i) + (startX + j));
            permutedImgB.swap(i * width + j, origWidth * (startY + i) + (startX + j));

            // [i*width + j] = origImg[origWidth*(startY+i)+(startX+j)];
        }
    }

    // println!("this is perm {:?}",perm);
    let (permImagePolyR, _) = vec_to_poly(permutedImgR.clone());
    let (permImagePolyG, _) = vec_to_poly(permutedImgG.clone());
    let (permImagePolyB, _) = vec_to_poly(permutedImgB.clone());

    permProve::<F, E, PCS>(
        nv,
        perm.clone(),
        origImgR,
        permImagePolyR.clone(),
        &pcs_param,
        &ver_param,
        transcript,
        transcriptTEST,
    );

    let permsliceR = &permutedImgR[0..croppedImgR.evaluations.len()];
    let (restrictedPolyR, _) = vec_to_poly(permsliceR.to_vec());

    permProve::<F, E, PCS>(
        nv,
        perm.clone(),
        origImgG,
        permImagePolyG.clone(),
        &pcs_param,
        &ver_param,
        transcript,
        transcriptTEST,
    );
    let permsliceG = &permutedImgG[0..croppedImgG.evaluations.len()];
    let (restrictedPolyG, _) = vec_to_poly(permsliceG.to_vec());

    permProve::<F, E, PCS>(
        nv,
        perm.clone(),
        origImgB,
        permImagePolyB.clone(),
        &pcs_param,
        &ver_param,
        transcript,
        transcriptTEST,
    );
    let permsliceB = &permutedImgB[0..croppedImgR.evaluations.len()];
    let (restrictedPolyB, _) = vec_to_poly(permsliceB.to_vec());
    //We first assume powers of two...
    let mut differencePolyR = VirtualPolynomial::new_from_mle(&restrictedPolyR, F::one());
    differencePolyR.add_mle_list([croppedImgR], -F::one());
    let mut differencePolyG = VirtualPolynomial::new_from_mle(&restrictedPolyG, F::one());
    differencePolyG.add_mle_list([croppedImgG], -F::one());
    let mut differencePolyB = VirtualPolynomial::new_from_mle(&restrictedPolyB, F::one());
    differencePolyB.add_mle_list([croppedImgB], -F::one());
    let proof = <PolyIOP<F> as ZeroCheck<F>>::prove(&differencePolyR, transcript).unwrap();
    let proof = <PolyIOP<F> as ZeroCheck<F>>::prove(&differencePolyG, transcript).unwrap();
    let proof = <PolyIOP<F> as ZeroCheck<F>>::prove(&differencePolyB, transcript).unwrap();

    //Do zero check thing
}
// pub fn pubAffineLinCheck<F: PrimeField, E, PCS>(
//     nv: usize,
//     // perm: Vec<F>,
//     origImgR: Arc<DenseMultilinearExtension<F>>,
//     origImgG: Arc<DenseMultilinearExtension<F>>,
//     origImgB: Arc<DenseMultilinearExtension<F>>,
//     croppedImgR: Arc<DenseMultilinearExtension<F>>,
//     croppedImgG: Arc<DenseMultilinearExtension<F>>,
//     croppedImgB: Arc<DenseMultilinearExtension<F>>,
//     origWidth: usize,
//     origHeight: usize,
//     startX: usize,
//     startY: usize,
//     endX: usize,
//     endY: usize,
//     pcs_param: &PCS::ProverParam,
//     ver_param: &PCS::VerifierParam,
//     // point: PCS::Point,
//     // myRand: Vec<F>,
//     transcript: &mut IOPTranscript<E::ScalarField>,
//     transcriptTEST: &mut IOPTranscript<E::ScalarField>,
// )
