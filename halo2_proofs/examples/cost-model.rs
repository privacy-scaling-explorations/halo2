use gumdrop::Options;
use halo2_proofs::dev::cost_model::*;

/// CLI Options to build a circuit specifiction to measure the cost model of.
#[derive(Debug, Options)]
struct CliCostOptions {
    #[options(help = "Print this message.")]
    help: bool,

    #[options(
        help = "An advice column with the given rotations. May be repeated.",
        meta = "R[,R..]"
    )]
    advice: Vec<Poly>,

    #[options(
        help = "An instance column with the given rotations. May be repeated.",
        meta = "R[,R..]"
    )]
    instance: Vec<Poly>,

    #[options(
        help = "A fixed column with the given rotations. May be repeated.",
        meta = "R[,R..]"
    )]
    fixed: Vec<Poly>,

    #[options(help = "Maximum degree of the custom gates.", meta = "D")]
    gate_degree: usize,

    #[options(
        help = "A lookup over N columns with max input degree I and max table degree T. May be repeated.",
        meta = "N,I,T"
    )]
    lookup: Vec<Lookup>,

    #[options(help = "A permutation over N columns. May be repeated.", meta = "N")]
    permutation: Vec<Permutation>,

    #[options(free, required, help = "2^K bound on the number of rows.")]
    k: usize,
}

impl CliCostOptions {
    fn to_cost_options(&self) -> CostOptions {
        CostOptions {
            advice: self.advice.clone(),
            instance: self.instance.clone(),
            fixed: self.fixed.clone(),
            gate_degree: self.gate_degree,
            lookup: self.lookup.clone(),
            permutation: self.permutation.clone(),
            k: self.k,
        }
    }
}

fn main() {
    let opts = CliCostOptions::parse_args_default_or_exit();
    let c = ModelCircuit::from(opts.to_cost_options());
    println!("{:#?}", c);
    println!(
        "Proof size: {} bytes",
        c.proof_size::<32, 32>(CommitmentScheme::IPA)
    );
}
