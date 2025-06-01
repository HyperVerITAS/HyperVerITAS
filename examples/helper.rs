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

//For nv = 15, we should do polyforT 32771 with corresponding 69643
//For nv = 10, we should do polyforT 1033 with corresponding 2053
//For nv = 11, we should do polyforT 2053 with corresp 4179
//We just now add
//13 corresp 8219
//14 corresp 16707
// 9 corresp 529
//8 corresp 285
//We pad with 0s for deg 0 and deg 1, as no prim poly for those...
pub const irredPolyTable: &[u32] = &[
    0, 0, 7, 11, 19, 37, 67, 131, 285, 529, 1033, 2053, 4179, 8219, 16707, 32771, 69643, 131081,
    262273, 524327, 1048585, 2097157, 4194307, 8388641, 16777351, 33554441, 67108935,
];
pub const flagUseCommits: bool = false;
// const STRINGS: &[&str] = &["str1", "str2"];
//This function takes in a vector representing our image and creates the appropriate polynomial.

pub fn vec_to_poly<F: PrimeField>(vec: Vec<F>) -> (Arc<DenseMultilinearExtension<F>>, F) {
    let mut size = (vec.len()).next_power_of_two() - 1;
    let mut nv = 0;
    //We get how much we'll have to pad the image vector.
    while size > 0 {
        size = size >> 1;
        nv += 1;
    }
    //We create the vector that will define our polynomial.
    let mut myVec = Vec::with_capacity(1 << nv);
    let mut sum = F::zero();
    //We fill our new vector in with old vector valeus(we can't copy as our new vector is one of field elements instead of u8)
    for i in vec.iter() {
        // let bytes = vec![i.clone()];
        // let n = F::from_le_bytes_mod_order(&bytes);
        myVec.push(*i);
        sum += i;
    }
    //We do appropriate padding
    for _ in 0..((1 << nv) - vec.len()) {
        myVec.push(F::zero());
    }
    //We convert to a dense multilinear extension, then convert this to a virtual polynomial.
    return (
        Arc::new(DenseMultilinearExtension::from_evaluations_vec(nv, myVec)),
        sum,
    );
}

//This is grayscale

//This is the function that checks if the multiplication for the image and matrix correctly produces the hash.
pub fn matrix_mult_check<F: PrimeField, E, PCS>(
    hash_matrix_as_poly: Arc<DenseMultilinearExtension<F>>,
    image_as_poly: Arc<DenseMultilinearExtension<F>>,
    digest_as_poly: Arc<DenseMultilinearExtension<F>>,
    randomness: Vec<F>,
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
    //This is the polynomial in b of F_M(r,b)
    let now = Instant::now();
    let (hash_matrix_poly, throwaway1) = matrix_poly(
        VirtualPolynomial::new_from_mle(&hash_matrix_as_poly.clone(), F::one()),
        randomness.clone(),
    );
    let elapsed_time = now.elapsed();
    println!(
        "Running matrix_poly took {} seconds.",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    //The poly matrixCombined is F_M(r,b)
    let mut matrixCombined = VirtualPolynomial::new_from_mle(&hash_matrix_poly, F::one());
    //The poly matrixCombined is F_M(r,b)*Im(b) (NO MORE CHANGES)
    matrixCombined.mul_by_mle(image_as_poly.clone(), F::one());
    //This is hash digest as poly
    let mut digest_poly = VirtualPolynomial::new_from_mle(&digest_as_poly, F::one());

    let pt = &randomness.clone();
    //Let f_h be the digest poly. This is f_h(r).
    //This is prover work.

    //We print pt
    print!("THIS IS PT {:?}\n", pt);
    print!("THIS IS DIGEST POLY {:?}\n", digest_poly);

    let f_h_of_r = digest_poly.evaluate(pt).unwrap();
    let mut transcript = <PolyIOP<F> as SumCheck<F>>::init_transcript();
    let proof = <PolyIOP<F> as SumCheck<F>>::prove(&matrixCombined, &mut transcript).unwrap();
    let poly_info = matrixCombined.aux_info.clone();
    //This is verifier work
    let now = Instant::now();

    let mut transcript = <PolyIOP<F> as SumCheck<F>>::init_transcript();
    let subclaim =
        <PolyIOP<F> as SumCheck<F>>::verify(f_h_of_r, &proof, &poly_info, &mut transcript).unwrap();
    // subclaim.expected_evaluation

    //Prover makes commitments to appropriate objects
    let hash_matrix_comm = PCS::commit(pcs_param, &hash_matrix_as_poly.clone()).unwrap();
    let img_matrix_comm: <PCS as PolynomialCommitmentScheme<E>>::Commitment =
        PCS::commit(pcs_param, &image_as_poly.clone()).unwrap();

    //Verifier confiroms value of F_M(r1, r2) where r2 is from subclaim eval and r1=r from earlier.
    let mut evalPt = subclaim.point.clone();
    // evalPt.reverse();
    let mut randPtMut = randomness.clone();
    // randPtMut.reverse();
    evalPt.append(&mut randPtMut);
    //Prover opens commitments at appropriate points
    let (openProof, Eval) = PCS::open(pcs_param, &hash_matrix_as_poly, &evalPt.clone()).unwrap();
    let (openProof2, Eval2) =
        PCS::open(pcs_param, &image_as_poly.clone(), &subclaim.point.clone()).unwrap();
    println!(
        "Prover time took {} seconds.",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    let now = Instant::now();

    //Verifier sees if they accept valuation proofs
    let verCheck1 = PCS::verify(
        &ver_param.clone(),
        &hash_matrix_comm.clone(),
        &evalPt.clone(),
        &Eval.clone(),
        &openProof.clone(),
    )
    .unwrap();
    // print!("Truth of FIRST OPENING VALUE {:?}\n", verCheck1);
    let verCheck2 = PCS::verify(
        &ver_param.clone(),
        &img_matrix_comm.clone(),
        &subclaim.point.clone(),
        &Eval2.clone(),
        &openProof2.clone(),
    )
    .unwrap();
    // print!("Truth of SECOND OPENINGVALUE {:?}\n", verCheck1);
    print!(
        "VERIFIER ACCEPTS FOR MATRIX MULT {:?}\n",
        Eval * Eval2 == subclaim.expected_evaluation && verCheck1 && verCheck2
    );

    // subclaim.point
    // print!("right subclaim - Image times hash matrix is consistent with digest\n");
    let elapsed_time = now.elapsed();
    println!(
        "Verifier time took {} seconds.",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    return 0;
}

//This function takes the virtual polynomial coressponding to our matrix, and returns the polynomial on the smaller hypercube F_M(r,b), along with its sum.
pub fn matrix_poly<F: PrimeField>(
    matrix_as_poly: VirtualPolynomial<F>,
    randomness: Vec<F>,
) -> (Arc<DenseMultilinearExtension<F>>, F) {
    let nv = matrix_as_poly.aux_info.num_variables - randomness.len();
    //Let f_M be our matrix as poly. This poly is f_M(r1,..,r_n,b). Where b is hypercube of size nv(M)-nv(r).
    let mut F_M = Vec::with_capacity(1 << nv);
    let mut sum = F::zero();
    let mut evalPtAsVec = Vec::new();
    let mut rand = Vec::new();
    rand.clone_from(&randomness);

    //We anticipate it to be of form F(b,r). Bits are read backwards (1100 corresponds to the number 3).
    let mut profileEvals = 0;
    let mut profileCreatePts = 0;
    for i in 0..1 << nv {
        let now = Instant::now();

        evalPtAsVec.clear();
        rand.clone_from(&randomness);

        // evalPtAsVec.clone_from(&randomness);
        for j in 0..(nv) {
            if ((i >> j) & 1 == 1) {
                evalPtAsVec.push(F::one());
            } else {
                evalPtAsVec.push(F::zero());
            }
        }
        // print!("This is rand {:?}\n", rand);

        evalPtAsVec.append(&mut rand);
        // print!("This is evalPtAsVec {:?}\n", evalPtAsVec);

        //We now evaluate our polynomial at the correct place.

        //We first create our evaluation point
        profileCreatePts += now.elapsed().as_millis();

        let pt = &evalPtAsVec;
        let now = Instant::now();
        let evalPt = matrix_as_poly.evaluate(pt).unwrap();
        profileEvals += now.elapsed().as_millis();

        F_M.push(evalPt);
        sum += evalPt;
        // print!("This is sum {:?}\n", evalPt);
        // print!("This is pt {:?}\n", pt);
        // print!("this is num var {:?}\n", nv);
    }
    println!("evaluations took {} seconds.", profileEvals / 1000);
    println!(
        "creating eval pts took {} seconds.",
        profileCreatePts / 1000
    );

    return (
        Arc::new(DenseMultilinearExtension::from_evaluations_vec(nv, F_M)),
        sum,
    );
}

pub fn multsetProve<F: PrimeField, E, PCS>(
    nv: usize,
    p1: &[Arc<DenseMultilinearExtension<F>>],
    p2: &[Arc<DenseMultilinearExtension<F>>],
    pcs_param: &PCS::ProverParam,
    ver_param: &PCS::VerifierParam,
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
    let proverTotal = Instant::now();
    //We make the final query point for prod check.
    let mut point = vec![F::one(); nv];
    // the point has to be reversed because Arkworks uses big-endian.
    point[0] = F::one() - F::one();

    let now = Instant::now();
    //We make randomness
    //fx and gx store the polynomials f(x)+r and g(x)+r
    //We make fiat transform vector here
    // let mut transcript = <PolyIOP<E::ScalarField> as ProductCheck<E, PCS>>::init_transcript();
    let alpha = transcript.get_and_append_challenge(b"alpha").unwrap();
    let alpha2 = transcriptTEST.get_and_append_challenge(b"alpha").unwrap();

    let constVec = vec![alpha; 1 << nv];
    let constFuncAsPoly = Arc::new(DenseMultilinearExtension::from_evaluations_slice(
        nv, &constVec,
    ));
    let now = Instant::now();
    let mut proverTime = now.elapsed().as_millis();

    let mut fx = vec![Arc::new(p1[0].as_ref() + constFuncAsPoly.as_ref())];
    let mut gx = vec![Arc::new(p2[0].as_ref() + constFuncAsPoly.as_ref())];
    // let mut fx = vec![Arc::new(p1[0].as_ref())];
    // let mut gx = vec![Arc::new(p2[0].as_ref())];

    //For multiple variables, we want r_0f_0x(x) + r_1f_1(x) +...+ r_nf_n(x)
    let elapsed_time = now.elapsed();

    println!(
        "THIS IS TIME FOR PROVER TO INSTANTIATE fx, gx {:?}",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );

    println!("THIS p1 LEN {:?}", p1.len());
    for i in 1..(p1.len()) {
        //We get new random challenges each time
        let alpha = transcript.get_and_append_challenge(b"alpha").unwrap();
        let alpha2 = transcriptTEST.get_and_append_challenge(b"alpha").unwrap();

        // let constVec = vec![alpha; 1 << nv];
        // let constFuncAsPoly = Arc::new(DenseMultilinearExtension::from_evaluations_slice(
        //     nv, &constVec,
        // ));
        //We now generate r_i * f_i
        let mut p1_plus_r = Vec::new();
        let mut p2_plus_r = Vec::new();

        //We build r_jf_j(x).
        let p1iEvals = p1[i].to_evaluations();
        let p2iEvals = p2[i].to_evaluations();
        let now3 = Instant::now();

        for j in 0..p1[0].to_evaluations().len() {
            p1_plus_r.push(p1iEvals[j] * alpha);
            p2_plus_r.push(p2iEvals[j] * alpha);
        }
        let elapsed_time = now3.elapsed();

        println!(
            "THIS IS CREATING alpha times f_0 {:?}",
            elapsed_time.as_millis() as f64 / 1000 as f64
        );
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
    let elapsed_time = now.elapsed();
    println!(
        "TIME TO MAKE COMMITMENT POLYNOMIALS {:?}",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    // let mut fx1 = Vec::new();
    // fx1[0] = Arc::new([VirtualPolynomial::new_from_mle(&p1[0], F::one())]);;
    let now = Instant::now();
    //This proves the productcheck.
    let (proof, prod_x, frac_poly) =
        <PolyIOP<E::ScalarField> as ProductCheck<E, PCS>>::prove(&pcs_param, &fx, &gx, transcript)
            .unwrap();
    let elapsed_time = now.elapsed();

    println!(
        "THIS IS TIME FOR PROVER TO DO PROD CHECK BUSINESS {:?}",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    let now = Instant::now();

    let prod_x_comm = PCS::commit(pcs_param, &prod_x).unwrap();
    let frac_comm = PCS::commit(pcs_param, &frac_poly).unwrap();
    let g_comm = PCS::commit(pcs_param, &gx[0]).unwrap();
    let f_comm = PCS::commit(pcs_param, &fx[0]).unwrap();
    let (openProof, Eval) = PCS::open(pcs_param, &prod_x, &point.clone()).unwrap();
    let elapsed_time = now.elapsed();
    println!(
        "THIS IS TIME FOR PROVER TO DO COMMIT CHECK BUSINESS +
        {:?}",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    proverTime += now.elapsed().as_millis();

    // return (proof,nv, fx.len());
    //-- WE DO VERIFIER WORK------------------------------------------------------------------------------------------------------------------------------------------
    // transcript
    //     .append_message(b"testing", b"initializing transcript for testing")
    //     .unwrap();

    //We recreate transcript. In our case, we shadow know that it's just some comm.

    // what's aux_info for? -- This was present in the code beforehand. I assume it's to ensure prod check works.
    let now = Instant::now();

    let aux_info: VPAuxInfo<<E as Pairing>::ScalarField> = VPAuxInfo {
        max_degree: fx.len() + 1,
        num_variables: nv,
        phantom: PhantomData,
    };

    let mut transcriptForAlpha = transcriptTEST.clone();
    transcriptForAlpha.append_serializable_element(b"frac(x)", &frac_comm);
    transcriptForAlpha.append_serializable_element(b"prod(x)", &prod_x_comm);
    let alpha = transcriptForAlpha
        .get_and_append_challenge(b"alpha")
        .unwrap();
    println!("MADE IT");
    let prod_subclaim = <PolyIOP<E::ScalarField> as ProductCheck<E, PCS>>::verify(
        &proof,
        &aux_info,
        transcriptTEST,
    )
    .unwrap();

    //TIMING STUFF

    //We do opening here. We check that the eval pt for multcheck evaluates to 1
    //WE NOW TEST VERIFY
    println!("ABOUT TO RUN VER CHECK");
    let verCheck1 = PCS::verify(
        &ver_param.clone(),
        &prod_x_comm.clone(),
        &point,
        &Eval.clone(),
        &openProof.clone(),
    )
    .unwrap();

    //We check if eval was computed correctly and that it is 1.
    if (Eval == F::one() && verCheck1) {
        print!("Correct\n");
    } else {
        print!("Incorrect Eval {:?} verCheck1 {:?}\n", Eval, verCheck1);
    }

    //We also need to check that the sumcheck invoked was computed correctly. We call sumcheck on a crazy polynomial...

    //GET OUR POINT THAT WE EVALUATE AT AS PT
    let evalPt = prod_subclaim.zero_check_sub_claim.point;

    //OUR EXPECTED EVAL IS THE FOLLOWING

    let expectEval = prod_subclaim.zero_check_sub_claim.expected_evaluation;

    //WE NOW CONSTRUCT OUR EXPECTEVAL FROM objects we know. Prover first supplies us with some objects
    let now = Instant::now();

    //Get evals for p1(x)
    let mut evalPtSansLast = Vec::<F>::new();
    let mut counter = 0;
    for a in evalPt.iter() {
        if counter != 0 {
            evalPtSansLast.push(*a);
        }
        counter += 1;
    }
    let mut evalPt0 = evalPtSansLast.clone();
    evalPt0.push(F::zero());

    let elapsed_time = now.elapsed();

    let mut verTime = now.elapsed().as_millis();
    let now: Instant = Instant::now();

    let (openFrac0, fracEval0) = PCS::open(pcs_param, &frac_poly, &evalPt0.clone()).unwrap();
    let (openProd0, prodEval0) = PCS::open(pcs_param, &prod_x, &evalPt0.clone()).unwrap();
    //Get evals for p2(x)
    let mut counter = 0;
    let mut evalPt1 = evalPtSansLast.clone();
    evalPt1.push(F::one());

    let (openFrac1, fracEval1) = PCS::open(pcs_param, &frac_poly, &evalPt1.clone()).unwrap();
    let (openProd1, prodEval1) = PCS::open(pcs_param, &prod_x, &evalPt1.clone()).unwrap();
    //get evals for frac(x)
    let (openFrac, fracEval) = PCS::open(pcs_param, &frac_poly, &evalPt.clone()).unwrap();
    //get eval for prod(x)
    let (openProd, prodEval) = PCS::open(pcs_param, &prod_x, &evalPt.clone()).unwrap();

    //get evals for g(x)
    let (openg, gEval) = PCS::open(pcs_param, &gx[0], &evalPt.clone()).unwrap();

    //get evals for f(x)
    let (openf, fEval) = PCS::open(pcs_param, &fx[0], &evalPt.clone()).unwrap();
    //Assume prover doesn't have to do openings, and verifier has access.
    let elapsed_time = now.elapsed();
    proverTime += now.elapsed().as_millis();
    println!(
        "THIS IS TIME FOR PROVER TO DO OPENINGS FOR RANGE+
        {:?}",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    // proverTime += now.elapsed().as_millis();
    // println!(
    //     "THIS IS TIME FOR PROVER TO DO OPENINGS  +
    //     {:?}\n",
    //     now.elapsed().as_millis() as f64 / 1000 as f64
    // );
    let now = Instant::now();

    //VERIFIER COMPUTATION

    let verCheck1 = PCS::verify(
        &ver_param.clone(),
        &frac_comm.clone(),
        &evalPt0.clone(),
        &fracEval0.clone(),
        &openFrac0.clone(),
    )
    .unwrap();
    let verCheck2 = PCS::verify(
        &ver_param.clone(),
        &prod_x_comm.clone(),
        &evalPt0.clone(),
        &prodEval0.clone(),
        &openProd0.clone(),
    )
    .unwrap();

    let verCheck3 = PCS::verify(
        &ver_param.clone(),
        &frac_comm.clone(),
        &evalPt.clone(),
        &fracEval.clone(),
        &openFrac.clone(),
    )
    .unwrap();
    let verCheck4 = PCS::verify(
        &ver_param.clone(),
        &prod_x_comm.clone(),
        &evalPt.clone(),
        &prodEval.clone(),
        &openProd.clone(),
    )
    .unwrap();

    let verCheck5 = PCS::verify(
        &ver_param.clone(),
        &g_comm.clone(),
        &evalPt.clone(),
        &gEval.clone(),
        &openg.clone(),
    )
    .unwrap();
    let verCheck6 = PCS::verify(
        &ver_param.clone(),
        &f_comm.clone(),
        &evalPt.clone(),
        &fEval.clone(),
        &openf.clone(),
    )
    .unwrap();

    let eq_x_r_eval = eq_eval(&evalPt, &prod_subclaim.zero_check_sub_claim.init_challenge).unwrap();
    //GET EVALS OF auxilary P1 P2.
    let P1Eval = (F::one() - evalPt[0]) * fracEval0 + evalPt[0] * prodEval0;
    let P2Eval = (F::one() - evalPt[0]) * fracEval1 + evalPt[0] * prodEval1;
    let testEval =
        (prodEval - P1Eval * P2Eval + alpha * fracEval * gEval - alpha * fEval) / eq_x_r_eval;
    verTime += now.elapsed().as_millis();
    println!("THIS IS PROVER TIME IN MULTSET {:?}------------------------------------------------------------", proverTime as f64 / 1000 as f64);
    println!(
        "THIS IS VER TIME IN MULTSET {:?} ",
        verTime as f64 / 1000 as f64
    );

    // print!("TO GET EXPECTED EVALUATION WE FIRST GET THE EQ R THING {:?}\n",eq_x_r_eval);
    //EXAMPLE COMMIT
    // let img_matrix_comm: <PCS as PolynomialCommitmentScheme<E>>::Commitment = PCS::commit(pcs_param, &image_as_poly.clone()).unwrap();

    //EXAMPLE OPEN
    // let (openProof, Eval) = PCS::open(pcs_param,&hash_matrix_as_poly, &evalPt.clone()).unwrap();

    //EXAMPLE VERIFY OPENING
    // let verCheck1 = PCS::verify(&ver_param.clone(), &hash_matrix_comm.clone(), &evalPt.clone(), &Eval.clone(), &openProof.clone()).unwrap();

    //END VERIFIER WORK -------------------------------------------------------------------------------------------------------------------------------------------------------------
    //Why was this line necessary?
    // check_frac_poly::<E>(&frac_poly, fs, gs);
    // return proof;
}

//Adapted from web https://users.rust-lang.org/t/how-to-serialize-a-u32-into-byte-array/986
pub fn transform_u32_to_array_of_u8(x: u32) -> [u8; 4] {
    let b1: u8 = ((x >> 24) & 0xff) as u8;
    let b2: u8 = ((x >> 16) & 0xff) as u8;
    let b3: u8 = ((x >> 8) & 0xff) as u8;
    let b4: u8 = (x & 0xff) as u8;
    return [b4, b3, b2, b1];
}
pub fn transform_u128_to_array_of_u8(x: u128) -> [u8; 16] {
    let mut bytes = [0; 16];
    for i in 0..16 {
        bytes[15 - i] = ((x >> 8 * i) & 0xff) as u8;
    }

    // let b1 : u8 = ((x >> 24) & 0xffffffffffffffff) as u8;
    // let b2 : u8 = ((x >> 16) & 0xffffffffffffffff) as u8;
    // let b3 : u8 = ((x >> 8) & 0xffffffffffffffff) as u8;
    // let b4 : u8 = (x & 0xffffffffffffffff) as u8;
    return bytes;
}
pub fn permProve<F: PrimeField, E, PCS>(
    nv: usize,
    perm: Vec<F>,
    f: Arc<DenseMultilinearExtension<F>>,
    g: Arc<DenseMultilinearExtension<F>>,
    pcs_param: &PCS::ProverParam,
    ver_param: &PCS::VerifierParam,
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
    let now = Instant::now();
    //We make randomness
    //fx and gx store the polynomials f(x)+r and g(x)+r
    //We make fiat transform vector here
    // let mut transcript = <PolyIOP<E::ScalarField> as ProductCheck<E, PCS>>::init_transcript();
    // let alpha = transcript.get_and_append_challenge(b"alpha").unwrap();
    // let alpha2 = transcriptTEST.get_and_append_challenge(b"alpha").unwrap();

    //We first make sID and make a polynomial for it

    let mut sID = Vec::new();
    for i in 0..(1 << nv) {
        let bytes = transform_u32_to_array_of_u8(i);
        let n = F::from_le_bytes_mod_order(&bytes);
        sID.push(n);
    }

    println!("{:?}", sID.len());

    let sIDPoly = Arc::new(DenseMultilinearExtension::from_evaluations_vec(
        nv,
        sID.clone(),
    ));

    //We then take sSigma and make a polynomial for it.
    let sSigmaPoly = Arc::new(DenseMultilinearExtension::from_evaluations_vec(nv, perm));

    //We now make commitments
    let sIDCom = PCS::commit(pcs_param, &sIDPoly.clone()).unwrap();

    let sSigmaPolyCom = PCS::commit(pcs_param, &sSigmaPoly.clone()).unwrap();

    //We now run multsetcheck.
    // println!("PERMUTATIONS {:?} \n {:?}", sIDPoly.evaluations, sSigmaPoly.evaluations);
    // println!("VECTORS {:?} \n {:?} ", f.evaluations, g.evaluations);
    multsetProve::<F, E, PCS>(
        nv,
        &[sIDPoly, f],
        &[sSigmaPoly, g],
        pcs_param,
        ver_param,
        transcript,
        transcriptTEST,
    );

    //We are done.
}

//This makes a vector size n that is 0,1,2,3,...,255,0,1,2,... all the way up to size.
pub fn makeTestImg(size: usize, cap: usize) -> Vec<F> {
    let mut vec = Vec::new();
    for i in 0..size {
        let mut imod255 = i.clone();
        while imod255 > cap {
            imod255 -= cap
        }
        vec.push(F::from_le_bytes_mod_order(&[imod255.try_into().unwrap()]));
    }
    return vec;
}

pub fn makeTestImgDeleteSoon(size: usize, cap: usize) -> Vec<F> {
    let mut vec: Vec<Fp<ark_ff::MontBackend<ark_bls12_381::FrConfig, 4>, 4>> = Vec::new();
    vec.push(F::from_le_bytes_mod_order(&[1.try_into().unwrap()]));
    vec.push(F::from_le_bytes_mod_order(&[0.try_into().unwrap()]));

    for i in 2..size {
        let mut imod255 = i.clone();
        while imod255 > cap {
            imod255 -= cap
        }
        vec.push(F::from_le_bytes_mod_order(&[imod255.try_into().unwrap()]));
    }
    return vec;
}

pub fn makeConstImg(size: usize, val: usize) -> Vec<F> {
    let mut vec = Vec::new();
    for i in 0..size {
        vec.push(F::from_le_bytes_mod_order(&[val.try_into().unwrap()]));
    }
    return vec;
}
pub fn toFieldVec<F: PrimeField>(u8Vec: &[u8]) -> Vec<F> {
    let mut vec = Vec::new();
    for i in 0..u8Vec.len() {
        vec.push(F::from_le_bytes_mod_order(&[u8Vec[i]]));
    }
    return vec;
}
pub fn toFieldVecFri<F: From<u64>>(u64Vec: &[u64]) -> Vec<F> {
    u64Vec.iter().map(|&x| F::from(x)).collect()
}

//This is matrix A and vector v, returns h=Av
pub fn matrixMultWithVec<F: PrimeField>(
    numRows: usize,
    numCols: usize,
    A: &[F],
    v: &[F],
) -> Vec<F> {
    let mut h = Vec::new();
    for i in 0..numRows {
        let mut mySum = F::zero();
        for j in 0..numCols {
            mySum += A[i * numCols + j] * v[j];
        }
        h.push(mySum);
    }
    return h;
}

//This is matrix A and vector v, returns h=rA
pub fn vecMultWithMatrix<F: PrimeField>(
    numRows: usize,
    numCols: usize,
    A: &[F],
    r: &[F],
) -> Vec<F> {
    let mut rTa = Vec::new();
    for i in 0..numCols {
        let mut mySum = F::zero();
        for j in 0..numRows {
            // println!("{}", i + numRows * j);
            mySum += A[i + numCols * j] * r[j];
        }
        // println!("THIS IS MYSUM {}", mySum);
        rTa.push(mySum);
    }
    return rTa;
}

//We make range check. We assume max val is at most 255, we may change this later.
pub fn range_check<F: PrimeField, E, PCS>(
    nv: usize,
    maxVal: u32,
    p1: Arc<DenseMultilinearExtension<F>>,
    // myRand: Vec<F>,
    primPolyForT: u64, //We represent our polynomial for galois generator for our table
    // as bits representing the value at each index. That is, x^3+x+1 = 2^3 + 2^1 + 2^0 = 11.
    primPolyForH: u64, //This is our polynomial for galois generator for our auxilary h
    transcript: &mut IOPTranscript<E::ScalarField>,
    transcriptTEST: &mut IOPTranscript<E::ScalarField>,
    pcs_param: &PCS::ProverParam,
    ver_param: &PCS::VerifierParam,
) where
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
    let now: Instant = Instant::now();
    let now2: Instant = Instant::now();
    let proverTotal: Instant = Instant::now();

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
        //If we have overflow
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
    let elapsed_time = now2.elapsed();

    println!(
        "PROVER Time to make table time for h is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    let now2 = Instant::now();
    //We make the big h and corresponding +1 vector
    //---------------------------------------------------------------------------------------------------------------------------------------------------------------------

    //
    let mySize = maxVal as usize;
    let mut hTable: Vec<usize> = vec![0; (maxVal + 1).try_into().unwrap()];

    //We recall in hyperplonk that for h, they need to count how many times each element of the vector(in our case, image) appears in the table. This code creates a table that encapsulates this.
    for a in &p1.evaluations {
        let mut b = a.to_string();
        if (b == "") {
            b = "0".to_string();
        }
        // print!("{:?}\n", b);
        //NOTE THIS WILL THROW IF WE TRY TO TEST WITH A VECTOR THAT IS OUT OF BOUNDS
        hTable[b.parse::<usize>().unwrap()] += 1;
    }
    let elapsed_time = now2.elapsed();
    println!(
        "PROVER Time to count num each eval appears is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    let now2 = Instant::now();
    let mut embeddedH: Vec<F> = vec![F::zero(); 2 << nv];
    let mut plusOneEmbeddedH: Vec<F> = vec![F::zero(); 2 << nv];
    //This takes the coefficients of our poly that aren't the most significant one. We note this is twice as big as table
    let galoisRepH = (primPolyForH) - (2 << nv);
    //This is how big our table is
    let size = 2 << nv;
    let mut binaryString: u64 = 1;

    //We create the table by setting index i to g^i(1) where g is our generator.
    let mut counter = 0;
    for a in &hTable {
        //We note that for each element in table, h has that element "consecutively"(relative to the generator function) a+1 times where a is the number of times it appears in our image.
        embeddedH[binaryString as usize] =
            F::from_le_bytes_mod_order(&transform_u32_to_array_of_u8(counter));
        binaryString <<= 1;
        //If we have overflow
        if (binaryString & size != 0) {
            //We utilize the equivalence relation
            binaryString ^= galoisRepH;
        }
        //We remove overflow
        binaryString = (size - 1) & binaryString;

        //Binarystring is now g^i(1).
        //We set table_{g^i(1)}= T_i. In this implementation, we assume that the maxval is less than or equal to 255.
        plusOneEmbeddedH[binaryString as usize] =
            F::from_le_bytes_mod_order(&transform_u32_to_array_of_u8(counter));
        for i in 0..*a {
            embeddedH[binaryString as usize] =
                F::from_le_bytes_mod_order(&transform_u32_to_array_of_u8(counter));
            binaryString <<= 1;

            //If we have overflow
            if (binaryString & size != 0) {
                //We utilize the equivalence relation
                binaryString ^= galoisRepH;
            }
            //We remove overflow
            binaryString = (size - 1) & binaryString;
            //Binarystring is now g^i(1).
            //We set table_{g^i(1)}= T_i. In this implementation, we assume that the maxval is less than or equal to 255.
            // print!("{:?}\n", binaryString);
            plusOneEmbeddedH[binaryString as usize] =
                F::from_le_bytes_mod_order(&transform_u32_to_array_of_u8(counter));
        }

        if (counter < maxVal) {
            counter += 1;
        }
    }
    let elapsed_time = now2.elapsed();

    println!(
        "PROVER Time to make +1 table for h is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );
    let now2 = Instant::now();
    //------------------------------------------------------------------------------------------------------------------------------------------------
    //We now make the appropriate polynomials
    let polyEmbeddedH = DenseMultilinearExtension::from_evaluations_vec(nv + 1, embeddedH.clone());

    let polyPlusOneEmbeddedH =
        DenseMultilinearExtension::from_evaluations_vec(nv + 1, plusOneEmbeddedH.clone());

    let polyTable = DenseMultilinearExtension::from_evaluations_vec(nv, embeddedTable.clone());
    let polyPlusOneTable =
        DenseMultilinearExtension::from_evaluations_vec(nv, plusOneTable.clone());

    let g1 = merge_polynomials::<F>(&[p1.clone(), Arc::new(polyTable)]).unwrap();
    let g2 = merge_polynomials::<F>(&[p1.clone(), Arc::new(polyPlusOneTable)]).unwrap();
    //Timing if we are just timing the creation of polynomials.
    let proverTime = now.elapsed().as_millis();

    let mut final_query = vec![F::one(); nv + 1];
    // the point has to be reversed because Arkworks uses big-endian.
    final_query[0] = F::one() - F::one();
    let elapsed_time = now2.elapsed();
    println!(
        "PROVER Time to Polynomials for h time for h is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );

    let final_eval = F::one();
    let now2 = Instant::now();
    let polyEmbeddedH_comm =
        PCS::commit(pcs_param.clone(), &Arc::new(polyEmbeddedH.clone())).unwrap();
    let elapsed_time = now2.elapsed();

    println!(
        "PROVER Time to make commitment to h is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );

    let now2 = Instant::now();
    let (openProofH, Eval) = PCS::open(
        pcs_param,
        &Arc::new(polyEmbeddedH.clone()),
        &vec![F::zero(); nv + 1],
    )
    .unwrap();
    let elapsed_time = now2.elapsed();
    println!(
        "PROVER Time to make open proof for h is {:?} seconds \n",
        elapsed_time.as_millis() as f64 / 1000 as f64
    );

    //TIMING IF INCLUDING OPEN AND COMMIT PROOFS
    // let proverTime = now.elapsed().as_millis();

    let elapsed_timeProver = proverTotal.elapsed();
    println!(
        "PROVER TOTAL TIME IN RANGE CHECK IS {} SECONDS.-------------------------------------------------------------------------------",
        elapsed_timeProver.as_millis() as f64 / 1000 as f64
    );
    multsetProve::<F, E, PCS>(
        nv + 1,
        &[g1.clone(), g2],
        &[Arc::new(polyEmbeddedH), Arc::new(polyPlusOneEmbeddedH)],
        &pcs_param,
        &ver_param,
        // final_query,
        transcript,
        transcriptTEST,
    );
    let now = Instant::now();

    let verCheck1 = PCS::verify(
        &ver_param.clone(),
        &polyEmbeddedH_comm.clone(),
        &vec![F::zero(); nv + 1].clone(),
        &Eval.clone(),
        &openProofH.clone(),
    )
    .unwrap();
    let verTime = now.elapsed().as_millis();

    print!(
        "Accept if we accept in multset as well {:?}\n",
        verCheck1 && Eval == F::zero()
    );
    print!(
        "THIS IS PROVER TIME IN RANGE WITHOUT MULTSET {:?}\n",
        proverTime as f64 / 1000 as f64
    );

    print!(
        "THIS IS VERTIME IN RANGE WITHOUT MULTSET {:?}\n",
        verTime as f64 / 1000 as f64
    );
}

//MULT A MATRIX AND A SPARSE VECTOR
pub fn matSparseMultVec<F: PrimeField>(
    numRows: usize,
    numCols: usize,
    sprseRep: &[Vec<(usize, F)>],
    r: &[F],
) -> Vec<F> {
    let mut Ar = Vec::new();
    for i in 0..numRows {
        let mut mySum = F::zero();
        for j in 0..sprseRep[i].len() {
            mySum += sprseRep[i][j].1 * r[sprseRep[i][j].0];
        }
        // println!("THIS IS MYSUM {}", mySum);
        Ar.push(mySum);
    }
    return Ar;
}
