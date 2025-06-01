#![allow(warnings)]

use ark_ec::pairing::Pairing;
use core::num;
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
use super::helper::*;
use super::image::*;
use super::protocols::*;
use ark_ff::One;
use ark_std::{rand::RngCore as R, test_rng};
use itertools::Itertools;

pub fn multsetProverIOP<F: PrimeField, E, PCS>(
    nv: usize,
    p1: &[Arc<DenseMultilinearExtension<F>>],
    p2: &[Arc<DenseMultilinearExtension<F>>],
    pcs_param: &PCS::ProverParam,
    ver_param: &PCS::VerifierParam,
    transcript: &mut IOPTranscript<E::ScalarField>,
) -> (
    <PolyIOP<E::ScalarField> as ProductCheck<E, PCS>>::ProductCheckProof,
    Arc<DenseMultilinearExtension<F>>,
    Arc<DenseMultilinearExtension<F>>,
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
    //We make the final query point for prod check.
    //fx and gx store the polynomials f(x)+r and g(x)+r
    let alpha = transcript.get_and_append_challenge(b"alpha").unwrap();
    let constVec = vec![alpha; 1 << nv];
    let constFuncAsPoly = Arc::new(DenseMultilinearExtension::from_evaluations_slice(
        nv, &constVec,
    ));
    let mut fx: Vec<Arc<DenseMultilinearExtension<F>>> =
        vec![Arc::new(p1[0].as_ref() + constFuncAsPoly.as_ref())];
    let mut gx = vec![Arc::new(p2[0].as_ref() + constFuncAsPoly.as_ref())];
    //For multiple polynomials, we want fx to be r_0f_0x(x) + r_1f_1(x) +...+ r_nf_n(x), likewise gx
    //We add if we have multiple polynomials...
    for i in 1..(p1.len()) {
        //We get new random challenges each time
        let alpha = transcript.get_and_append_challenge(b"alpha").unwrap();
        let mut p1_plus_r = Vec::new();
        let mut p2_plus_r = Vec::new();
        let p1iEvals = p1[i].to_evaluations();
        let p2iEvals = p2[i].to_evaluations();

        //We now generate r_i * f_i
        for j in 0..p1[0].to_evaluations().len() {
            p1_plus_r.push(p1iEvals[j] * alpha);
            p2_plus_r.push(p2iEvals[j] * alpha);
        }
        let p1_j_plus_r_poly = Arc::new(DenseMultilinearExtension::from_evaluations_vec(
            nv, p1_plus_r,
        ));
        let p2_j_plus_r_poly = Arc::new(DenseMultilinearExtension::from_evaluations_vec(
            nv, p2_plus_r,
        ));

        // fx contains one poly, we have it as list for productcheck. This is simply fx += r_if_ix
        fx[0] = Arc::new(fx[0].as_ref() + p1_j_plus_r_poly.as_ref());
        gx[0] = Arc::new(gx[0].as_ref() + p2_j_plus_r_poly.as_ref());
    }
    //We now prove the productcheck. We take a copy of the transcript at this point in time.
    let mut transcriptTEST = transcript.clone();
    let (proof, prod_x, frac_poly) =
        <PolyIOP<E::ScalarField> as ProductCheck<E, PCS>>::prove(&pcs_param, &fx, &gx, transcript)
            .unwrap();
    //We return the prodcheck proof, as well as the prod and frac polynomials.
    return (proof, prod_x, frac_poly);
}

pub fn range_checkProverIOP<F: PrimeField, E, PCS>(
    nv: usize,
    maxVal: u32,
    p1: Arc<DenseMultilinearExtension<F>>,
    // myRand: Vec<F>,
    primPolyForT: u64, //We represent our polynomial for galois generator for our table
    // as bits representing the value at each index. That is, x^3+x+1 = 2^3 + 2^1 + 2^0 = 11.
    primPolyForH: u64, //This is our polynomial for galois generator for our auxilary h
    transcript: &mut IOPTranscript<E::ScalarField>,
    pcs_param: &PCS::ProverParam,
    ver_param: &PCS::VerifierParam,
) -> (
    <PolyIOP<E::ScalarField> as ProductCheck<E, PCS>>::ProductCheckProof,
    Arc<DenseMultilinearExtension<F>>,
    Arc<DenseMultilinearExtension<F>>,
    Arc<DenseMultilinearExtension<F>>,
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
    //We make the table and coressponding +1 table
    //----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    let mut embeddedTable: Vec<F> = vec![F::zero(); 1 << nv];
    let mut plusOneTable: Vec<F> = vec![F::zero(); 1 << nv];
    //This takes the coefficients of our poly that aren't the most significant one.
    let galoisRep = (primPolyForT) - (1 << nv);
    //This is how big our table is
    let size = 1 << nv;
    let mut binaryString: u64 = 1;
    //We create the table by setting index i to g^i(1) where g is our generator.
    for i in 1..(maxVal as usize + 1) {
        //We set T_{g^i(1)}=T_i=i
        embeddedTable[binaryString as usize] =
            F::from_le_bytes_mod_order(&transform_u32_to_array_of_u8(i as u32));
        //This represents a multiplication by x
        binaryString <<= 1;
        //If we have overflow, we remove it
        if (binaryString & size != 0) {
            //We utilize the equivalence relation
            binaryString ^= galoisRep;
        }
        //We remove overflow
        //Binarystring is now g^i(1).
        //We set table_{g^i(1)}= T_i. In this implementation, we assume that the maxval is less than or equal to 255.
        binaryString = (size - 1) & binaryString;
        //We now add to the plus one table.
        plusOneTable[binaryString as usize] =
            F::from_le_bytes_mod_order(&transform_u32_to_array_of_u8(i as u32));
    }

    //We make the big h and corresponding +1 vector
    //---------------------------------------------------------------------------------------------------------------------------------------------------------------------

    //
    let mut hTable: Vec<usize> = vec![0; (maxVal + 1).try_into().unwrap()];
    //We recall in hyperplonk that for h, they need to count how many times each element of the vector(in our case, image) appears in the table. This code creates a table that encapsulates this.
    for a in &p1.evaluations {
        let mut b = a.to_string();
        if (b == "") {
            b = "0".to_string();
        } else {
            // println!("{}", b);
            hTable[b.parse::<usize>().unwrap()] += 1;
        }
        // print!("{:?}\n", b);
        //NOTE THIS WILL THROW IF WE TRY TO TEST WITH A VECTOR THAT IS OUT OF BOUNDS
        hTable[b.parse::<usize>().unwrap()] += 1;
    }
    let mut embeddedH: Vec<F> = vec![F::zero(); 1 << nv];
    let mut plusOneEmbeddedH: Vec<F> = vec![F::zero(); 1 << nv];
    let size = 1 << nv;
    let mut binaryString: u64 = 1;

    //We create the table by setting index i to g^i(1) where g is our generator.
    let mut counter = 0;
    for a in &hTable {
        for i in 0..(*a + 1) {
            embeddedH[binaryString as usize] =
                F::from_le_bytes_mod_order(&transform_u32_to_array_of_u8(counter));
            binaryString <<= 1;

            //If we have overflow
            if (binaryString & size != 0) {
                //We utilize the equivalence relation
                binaryString ^= galoisRep;
            }
            //We remove overflow
            binaryString = (size - 1) & binaryString;
            //Binarystring is now g^i(1).
            //We set table_{g^i(1)}= T_i.
            plusOneEmbeddedH[binaryString as usize] =
                F::from_le_bytes_mod_order(&transform_u32_to_array_of_u8(counter));
        }

        if (counter < maxVal) {
            counter += 1;
        }
    }
    //--------------------------------------------------------------------EMBEDDINGS ARE DONE----------------------------------------------------------------------------
    //We now make the appropriate polynomials
    let definingH: DenseMultilinearExtension<F> =
        DenseMultilinearExtension::from_evaluations_vec(nv, embeddedH.clone());
    let definingPlusOneH: DenseMultilinearExtension<F> =
        DenseMultilinearExtension::from_evaluations_vec(nv, plusOneEmbeddedH.clone());

    let zeroVec = DenseMultilinearExtension::from_evaluations_vec(nv, vec![F::zero(); 1 << nv]);
    let polyEmbeddedH =
        merge_polynomials::<F>(&[Arc::new(zeroVec.clone()), Arc::new(definingH.clone())]).unwrap();

    let polyPlusOneEmbeddedH =
        merge_polynomials::<F>(&[Arc::new(zeroVec), Arc::new(definingPlusOneH)]).unwrap();

    let polyTable = DenseMultilinearExtension::from_evaluations_vec(nv, embeddedTable.clone());
    let polyPlusOneTable =
        DenseMultilinearExtension::from_evaluations_vec(nv, plusOneTable.clone());

    let g1 = merge_polynomials::<F>(&[p1.clone(), Arc::new(polyTable)]).unwrap();
    let g2 = merge_polynomials::<F>(&[p1.clone(), Arc::new(polyPlusOneTable)]).unwrap();
    //Timing if we are just timing the creation of polynomials.
    let (multsetProof, fx, gx) = multsetProverIOP::<F, E, PCS>(
        nv + 1,
        &[g1, g2],
        &[polyEmbeddedH.clone(), polyPlusOneEmbeddedH],
        &pcs_param,
        &ver_param,
        transcript,
    );

    //We make what the IOP returns.
    //Prover outside has to make open proof and commitments for h.

    // let polyEmbeddedH_comm = PCS::commit(pcs_param.clone(), &Arc::new(definingH.clone())).unwrap();
    // let (openProofH, Eval) = PCS::open(pcs_param,&Arc::new(definingH.clone()), &vec![F::zero();nv]).unwrap();
    //We return the multsetproof and corresponding prod and frac polies.
    return (multsetProof, fx, gx, Arc::new(definingH));
    // polyEmbeddedH_comm, definingH
}

pub fn cropProveAffineIOP<F: PrimeField>(
    nvOrig: usize,
    nvCrop: usize,
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
    // pcs_param: &PCS::ProverParam,
    // ver_param: &PCS::VerifierParam,
    // point: PCS::Point,
    // myRand: Vec<F>,
    transcript: &mut IOPTranscript<F>,
) -> (
    [<PolyIOP<F> as SumCheck<F>>::SumCheckProof;3]
    )
where
        // Polynomial = Arc<DenseMultilinearExtension<F>>,
        // Point = Vec<F>,
        // Evaluation = F,
    // >,
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
            cropPerm[initVal].push((counter, F::one()));
            counter += 1;
            initVal += 1;
        }
        initVal += origWidth - (width + 1);
    }
    // println!("Made it 2");

    // MAKE THIS COME FROM TRANSCRIPT
    let frievaldRand = Arc::new(DenseMultilinearExtension::rand(nvCrop, &mut rng));
    let mut frievaldRandVec = &frievaldRand.evaluations;
    // println!("Made it 2.2");

    // println!("{:?}", frievaldRandVec);
    // println!("{:?}", 1<<nvCrop);

    let now = Instant::now();
    let permTimesR = matSparseMultVec::<F>(1 << nvOrig, 1 << nvCrop, &cropPerm, &frievaldRandVec);
    let elapsed_timeProver = now.elapsed();
    println!(
        "Verifier/Prover time in PermTimesR is {} seconds.",
        elapsed_timeProver.as_millis() as f64 / 1000 as f64
    );

    // println!("Made it 2.5");
    let now = Instant::now();

    let permTimesRPoly = Arc::new(DenseMultilinearExtension::from_evaluations_vec(
        nvOrig,
        permTimesR.clone(),
    ));
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

    let mut IPermR = VirtualPolynomial::new_from_mle(&permTimesRPoly, F::one());
    let mut IPermG = VirtualPolynomial::new_from_mle(&permTimesRPoly, F::one());
    let mut IPermB = VirtualPolynomial::new_from_mle(&permTimesRPoly, F::one());

    //The poly matrixCombined is F_M(r,b)*Im(b) (NO MORE CHANGES)
    IPermR.mul_by_mle(origImgR.clone(), F::one());
    IPermG.mul_by_mle(origImgG.clone(), F::one());
    IPermB.mul_by_mle(origImgB.clone(), F::one());

    // let mut mySum2 = F::zero();
    // for i in 0..1<<nvOrig{
    //     mySum2 += permTimesR[i] * origImgR.evaluations[i];
    // }
    // println!("{}", mySum2);
    // println!("Made it 3");
    let now = Instant::now();
    let mut transcriptTest = transcript.clone();
    let proof0 = <PolyIOP<F> as SumCheck<F>>::prove(&IPermR, transcript).unwrap();
    let proof1 = <PolyIOP<F> as SumCheck<F>>::prove(&IPermG, transcript).unwrap();
    let proof2 = <PolyIOP<F> as SumCheck<F>>::prove(&IPermB, transcript).unwrap();
    let poly_info = IPermR.aux_info.clone();
    let elapsed_timeProver = now.elapsed();
    println!(
        "Time to run sumcheck IOP is {} seconds.",
        elapsed_timeProver.as_millis() as f64 / 1000 as f64
    );
    return [proof0, proof1, proof2];
   

}

pub fn cropProveOneAffineIOP<F: PrimeField>(
    nvOrig: usize,
    nvCrop: usize,
    origImgR: Arc<DenseMultilinearExtension<F>>,
    croppedImgR: Arc<DenseMultilinearExtension<F>>,
    origWidth: usize,
    origHeight: usize,
    startX: usize,
    startY: usize,
    endX: usize,
    endY: usize,
    transcript: &mut IOPTranscript<F>,
) -> (
    <PolyIOP<F> as SumCheck<F>>::SumCheckProof
    )
where
        // Polynomial = Arc<DenseMultilinearExtension<F>>,
        // Point = Vec<F>,
        // Evaluation = F,
    // >,
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
            cropPerm[initVal].push((counter, F::one()));
            counter += 1;
            initVal += 1;
        }
        initVal += origWidth - (width + 1);
    }
    // println!("Made it 2");

    // MAKE THIS COME FROM TRANSCRIPT
    let frievaldRand = Arc::new(DenseMultilinearExtension::rand(nvCrop, &mut rng));
    let mut frievaldRandVec = &frievaldRand.evaluations;
    // println!("Made it 2.2");

    // println!("{:?}", frievaldRandVec);
    // println!("{:?}", 1<<nvCrop);

    let now = Instant::now();
    let permTimesR = matSparseMultVec::<F>(1 << nvOrig, 1 << nvCrop, &cropPerm, &frievaldRandVec);
    let elapsed_timeProver = now.elapsed();
    println!(
        "Verifier/Prover time in PermTimesR is {} seconds.",
        elapsed_timeProver.as_millis() as f64 / 1000 as f64
    );

    // println!("Made it 2.5");
    let now = Instant::now();

    let permTimesRPoly = Arc::new(DenseMultilinearExtension::from_evaluations_vec(
        nvOrig,
        permTimesR.clone(),
    ));
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

    let mut IPermR = VirtualPolynomial::new_from_mle(&permTimesRPoly, F::one());

    //The poly matrixCombined is F_M(r,b)*Im(b) (NO MORE CHANGES)
    IPermR.mul_by_mle(origImgR.clone(), F::one());

    // let mut mySum2 = F::zero();
    // for i in 0..1<<nvOrig{
    //     mySum2 += permTimesR[i] * origImgR.evaluations[i];
    // }
    // println!("{}", mySum2);
    // println!("Made it 3");
    let now = Instant::now();
    let mut transcriptTest = transcript.clone();
    let proof0 = <PolyIOP<F> as SumCheck<F>>::prove(&IPermR, transcript).unwrap();
    let poly_info = IPermR.aux_info.clone();
    let elapsed_timeProver = now.elapsed();
    println!(
        "Time to run sumcheck IOP is {} seconds.",
        elapsed_timeProver.as_millis() as f64 / 1000 as f64
    );
    return proof0;
   

}