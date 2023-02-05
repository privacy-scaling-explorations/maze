# Maze

Maze is a cli based tool to build aggregation circuits and generate aggregated proofs for snarkjs circom-plonk proofs.

That means using Maze you can take a bunch of plonk proofs that you generate using snarkjs and aggregate them into a single proof using proof aggregation circuit.

## Getting started

### Install [this fork](https://github.com/Janmajayamall/snarkjs) of Snarkjs

> **Note:** this will override existing installation of [snarkjs](https://github.com/iden3/snarkjs) on your system.

```sh
git clone https://github.com/Janmajayamall/snarkjs
cd snarkjs
npm install
npm run build
npm run buildcli
npm install -g .
```

The fork implements two changes to original [snarkjs](https://github.com/iden3/snarkjs)

-   replaces hash function in transcript of plonk proofs from keccak to poseidon.
-   adds `snarkjs plonk setupmaze` cli command that generates plonk proof of circuit for several inputs and outputs necessary files (i.e. plonk verification key, proofs, and public signals of each proof) for building aggregation circuit using [maze]().

### Install maze

> You must have rust installed to build and install maze

```sh
git clone https://github.com/privacy-scaling-explorations/maze
cd maze/maze-cli
cargo build
cargo install --path .
```

You can check correctness of installation by running

```sh
maze --help
```

## How to use

Maze can build aggregation circuit to aggregate a pre-defined number of plonk-proofs. To generate individual plonk proofs for a circuit on different inputs we use [fork of snarkjs](https://github.com/Janmajayamall/snarkjs) we installed above. After which we use maze tool to necessary commands.

### 1. Create circuit

```sh
cat <<EOT > circuit.circom
pragma circom 2.0.0;

template Multiplier(n) {
    signal input a;
    signal input b;
    signal output c;

    signal int[n];

    int[0] <== a*a + b;
    for (var i=1; i<n; i++) {
	int[i] <== int[i-1]*int[i-1] + b + 3;
    }

    c <== int[n-1];
}

component main = Multiplier(1000);
EOT
```

### 2. Download ptau file

```sh
curl https://hermez.s3-eu-west-1.amazonaws.com/powersOfTau28_hez_final_15.ptau --output hez_15.ptau
```

The command above downloads and save `powersOfTau28_hez_final_15.ptau` as `hez_15.ptau`. You can find more info about file [here](https://github.com/iden3/snarkjs#7-prepare-phase-2).

You can instead choose to download a file with different max. constraints.

> Note that `tau` value used in `common reference string (CRS)` of commitment scheme in individual plonk proofs must be same as the one used in commitment scheme of aggregation circuit.

### 3. Run plonk setup

```sh
circom circuit.circom --r1cs --wasm
snarkjs plonk setup circuit.r1cs hez_15.ptau
```

### 4. Create inputs file

```sh
cat <<EOT > inputs.json
[
    {
        "a": 312,
        "b": 64
    },
    {
        "a": 344,
        "b": 21
    }
]
EOT
```

`inputs.json` file contains an array of inputs for which we desire to generate plonk proofs of the circuit. Here we limit to building aggregation circuit for 2 proofs.

### 5. Plonk setup maze

```sh
snarkjs plonk setupmaze inputs.json circuit_js/circuit.wasm circuit.zkey
```

The command generates

-   `verification_key.json`: plonk verification key for the circuit.
-   `proofs.json`: array of proofs for inputs in `inputs.json`.
-   `public_signals.json`: array of public signals corresponding to proofs in `proofs.json`.

> All three files are necessary for building aggregation circuit using maze.

### 6. Maze mock-setup

```sh
maze mock-setup verification_key.json proofs.json public_signals.json
```

Mock setup does the following

-   builds an aggregation circuit for the circom circuit with plonk verification key as `verification_key.json`. The maximum number of proofs that you can aggregate with this aggregation circuit equals number of proofs in `proofs.json`.
-   runs [mock prover](https://docs.rs/halo2_proofs/0.2.0/halo2_proofs/dev/struct.MockProver.html) on the aggregation circuit to check that all constraints satisfy.
-   Outputs `k`. `2^k` are the maximum number of rows your circuit needs, thus your CRS must of degree `2^k`.

### 7. Maze gen-evm-verifier

```sh
maze gen-evm-verifier verification_key.json proofs.json public_signals.json hez_22.srs outputs
```

`hez_22.srs` contains same CRS as `powersOfTau28_hez_final_22.ptau`. You can either use `.srs` or `.ptau` as `PARAMS`, but `.srs` files are smaller in size than `.ptau` files thus faster to read in memory.

Notice that we are using CRS file of k = 22.

`gen-evm-verifier` generates evm verifier bytecode for the aggregation circuit and stores it inside `outputs` directory.

### 8. Maze create-proof

```sh
maze create-proof verification_key.json proofs.json public_signals.json hez_22.srs outputs
```

`create-proof` generates proof for the aggregation circuit. Validation of the proof (followed by the pairing check of the final accumulator) by the verifier confirms the validity of plonk proofs inside `proofs.json`.

`create_proof` creates two files

-   `halo2-agg-proof.txt`: Contains only the proof in bytes of the aggregation circuit.
-   `halo2-agg-evm-calldata.txt`: Contains proof of aggregation circuit and instance values in bytes encoded as calldata input to evm verifier contract.

### 9. Maze verify-proof

```sh
maze verify-proof verification_key.json proofs.json public_signals.json outputs/halo2-agg-proof.txt hez_22.srs
```

`verify-proof` verifies the aggregated proof (stored in `halo2-agg-proof.txt`) generated using `create-proof`

### 10. Maze evm-verify-proof

```sh
maze evm-verify-proof outputs/halo2-agg-evm-calldata.txt outputs/evm-verifier.txt
```

`evm-verify-proof` simulates execution of EVM bytecode in `evm-verifier.txt` with calldata in `halo2-agg-evm-calldata.txt`.

## FAQs

### 1. .ptau and .srs files

.ptau and .srs are both file formats for storing CRS. .srs files are smaller in size than .ptau file. You can convert .ptau file to .srs file using this [repo](https://github.com/han0110/halo2-kzg-srs).

<!-- You can also find  -->

### 2. How expensive is proof aggregation ?

Machine used:

| individual circuit | aggregation circuit | no. of proofs | proving time (in seconds) | peak RAM (GB) | machine used              |
| ------------------ | ------------------- | ------------- | ------------------------- | ------------- | ------------------------- |
| PI = 1; k = 15     | k = 24              | 25            | 1621                      | 107 GB        | r5a.16xlarge ec2 instance |
| PI = 1; k = 15     | k = 25              | 50            | 3422                      | 214 GB        | r5a.16xlarge ec2 instance |

## Contact

Join our [telegram](https://t.me/+sysPCS8ImyI4YzI1) group for questions and discussions.

## Acknowledgements

-   [Han](https://github.com/han0110): For implementing [plonk-verifier](https://github.com/privacy-scaling-explorations/plonk-verifier) that maze heavily uses for building aggregation circuits. Also, for their discussions around several implementation details.
-   [PSE zKEVM team](https://github.com/privacy-scaling-explorations/halo2wrong): For implementing [halo2wrong](https://github.com/privacy-scaling-explorations/halo2wrong) and fork of [halo2](https://github.com/privacy-scaling-explorations/halo2) that replaces IPA commitment scheme with KZG.
-   [Halo2 team](https://github.com/zcash/halo2): For implementing [Halo2](https://github.com/zcash/halo2) library without which developing aggregation circuits will a lot harder.
