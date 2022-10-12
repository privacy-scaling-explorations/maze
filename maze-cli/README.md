# Maze

Maze is a cli based tool to build aggregation circuits and generate aggregated proofs for snarkjs circom-plonk proofs.

That means using Maze you can take a bunch of plonk proofs that you generate using snarkjs and aggregate them into a single proof using proof aggregation circuit.

## Getting started

### Install [this fork](https://github.com/Janmajayamall/snarkjs) Snarkjs

> Warning: this will override existing installation of snarkjs on your system.

```sh
git clone https://github.com/Janmajayamall/snarkjs
cd snarkjs
npm install
npm buildcli
npm install -g .
```

The fork implements two changes to original [snarkjs](https://github.com/iden3/snarkjs)

-   replaces hash function in transcript of plonk proofs from keccak to poseidon.
-   adds `snarkjs plonk setupmaze` cli command that generates plonk proof of circuit for several inputs and outputs necessary files (i.e. plonk verification key, proofs, and public signals of each proof) for building aggregation circuit using [maze]().

### Install maze

> You must have rust installed to build and install maze

```sh
git clone https://github.com/privacy-scaling-explorations/maze
cd maze-cli
cargo build
cargo install .
```

You can check correctness of installation by running

```sh
maze --help
```

## How to

Maze can build aggregation circuit to aggregate a pre-defined number of plonk-proofs. To generate individual plonk proofs for a circuit on different inputs we use [fork of snarkjs](https://github.com/Janmajayamall/snarkjs) we installed [above](). After which we use maze tool to necessary commands.

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

> `tau` value used for commitment scheme in individual plonk proofs must be same as the one used in commitment scheme of aggregation circuit.

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
-   runs [mock prover]() on the aggregation circuit to check that all constraints satisfy.
-   Outputs `k`. `2^k` are the maximum number of rows your circuit needs, thus your CRS must of degree `2^k`.

### 7. Maze gen-evm-verifier

```sh
maze gen-evm-verifier verification_key.json proofs.json public_signals.json hez_22.srs outputs
```

`hez_22.srs` contains same CRS as `powersOfTau28_hez_final_22.ptau`. You can either use `.srs` or `.ptau` as `PARAMS`, but `.srs` files are smaller in size than `.ptau` files thus faster to read in memory.

Notice that we are using CRS file for k = 22, since aggregation circuit consists of more constraints.

`gen-evm-verifier` generates evm verifier bytecode for the aggregation circuit and stores it inside `outputs` directory.

### 8. Maze create-proof

```sh
maze create-proof verification_key.json proofs.json public_signals.json hez_22.srs outputs
```

`create-proof` generates proof for the aggregation circuit. Validation of the proof (followed by the pairing check of the final accumulator) by the verifier confirms the validity of plonk proofs inside `proofs.json`.

`create_proof` creates two files

-   `halo2-agg-proof.txt`: Contains only the proof in bytes of the aggregation circuit.
-   `halo2-agg-evm-calldata.txt`: Contains proof of aggregation circuit and instance values in bytes encoded as calldata input to evm verifier.

### 9. Maze verify-proof

An aggregation circuit aggregates pre-defined number of individual proofs to produce an aggregated proof. In the following steps we use Circuit A. We first generate 3 plonk proofs on 3 different inputs for Circuit A using snarkjs. We then use maze tool to build an aggregation circuit and try out different commands available.

1. Perform plonk setup to product zkey
2. create inputs file
3. plonk setup maze to product necessary files

    To build the aggregation circuit we require 3 files
    (a) verification_key.json - plonk verification key of circuit A
    (b) proofs.json - contains `n` proofs.
    (c) publics.json - contains public signals correspoding to proofs
    (d) SRS/ptau file for aggregation circuit.

    Note: tau used for SRS in aggregation circuit must be same as one used to generate plonk proofs using snarkjs. For more details read here.

4. maze mock-setup
5. maze gen-evm-verifier
6. maze jdiwadjiawd

7. What is mock prover
8. How to choose k?
9. SRS vs Ptau
10.
