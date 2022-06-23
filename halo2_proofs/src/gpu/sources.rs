use crate::arithmetic::Group;
use ff_cl_gen as ffgen;
use pairing::bn256::{Fq, Fr};

// Instead of having a very large OpenCL program written for a specific curve, with a lot of
// rudandant codes (As OpenCL doesn't have generic types or templates), this module will dynamically
// generate OpenCL codes given different PrimeFields and curves.

static FFT_SRC: &str = include_str!("fft/fft.cl");
static FIELD2_SRC: &str = include_str!("multiexp/field2.cl");
static EC_SRC: &str = include_str!("multiexp/ec.cl");
static MULTIEXP_SRC: &str = include_str!("multiexp/multiexp.cl");

fn field2(field2: &str, field: &str) -> String {
    String::from(FIELD2_SRC)
        .replace("FIELD2", field2)
        .replace("FIELD", field)
}

fn fft(field: &str) -> String {
    String::from(FFT_SRC).replace("FIELD", field)
}

#[cfg(not(feature = "blstrs"))]
const BLSTRS_DEF: &str = "";
#[cfg(feature = "blstrs")]
const BLSTRS_DEF: &str = "#define BLSTRS";

fn ec(field: &str, point: &str) -> String {
    String::from(EC_SRC)
        .replace("FIELD", field)
        .replace("POINT", point)
        .replace("__BLSTRS__", BLSTRS_DEF)
}

fn multiexp(point: &str, exp: &str) -> String {
    String::from(MULTIEXP_SRC)
        .replace("POINT", point)
        .replace("EXPONENT", exp)
}

/// WARNING: This function works only with Short Weierstrass Jacobian curves with Fq2 extension field.
pub fn kernel<G>(limb64: bool) -> String
where
    G: Group,
{
    vec![
        if limb64 {
            ffgen::field::<Fr, ffgen::Limb64>("Fr")
        } else {
            ffgen::field::<Fr, ffgen::Limb32>("Fr")
        },
        fft("Fr"),
        if limb64 {
            ffgen::field::<Fq, ffgen::Limb64>("Fq")
        } else {
            ffgen::field::<Fq, ffgen::Limb32>("Fq")
        },
        ec("Fq", "G1"),
        multiexp("G1", "Fr"),
        field2("Fq2", "Fq"),
        ec("Fq2", "G2"),
        multiexp("G2", "Fr"),
    ]
    .join("\n\n")
}
