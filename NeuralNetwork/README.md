# Hopfield Networks

## Description
This repository contains Lean formalizations related to Hopfield Networks and Boltzmann Machines, written in the *Lean theorem prover* language. The project provides a certified specification for Hopfield networks, explores their convergence properties, and extends the framework to probabilistic models and statistical mechanics.

The project is organized into two main directories:

- **`NeuralNetwork/`**: Contains the core formalization of neural networks.
- **`Mathematics/`**: Contains supporting mathematical lemmas and structures.

Below is a brief overview of the key files in the `NeuralNetwork` directory:

- **`Core.lean`**: The root specification of a computable Hopfield network, including the energy function and proofs of convergence for deterministic updates.
- **`test.lean`** – Computations and implementation of the Hebbian learning algorithm.  

- **`TwoState.lean`**: Generalizes the core model to an abstract two-state neural network framework and introduces probabilistic Gibbs updates.
- **`Convergence.lean`**: Formalizes convergence for any system with a strict Lyapunov function (a "Strictly Hamiltonian" system).
- **`BoltzmannMachine.lean`**: Defines Boltzmann Machines as a specific instance of the two-state framework.
- **`DetailedBalanceBM.lean`** & **`DetailedBalanceGen.lean`**: Prove that the Gibbs sampling dynamics satisfy the detailed balance condition with respect to the Boltzmann distribution.
- **`Ergodicity.lean`**: Shows that the random-scan update kernel is ergodic, guaranteeing convergence to the unique stationary Boltzmann distribution.
- **`ZeroTemp.lean`**: Proves that in the zero-temperature limit, probabilistic Gibbs dynamics converge to the deterministic update rule.
- **`toCanonicalEnsemble.lean`**: Provides a bridge from the network's energy specification to the formal framework of statistical mechanics (canonical ensembles).
- **`NeuralNetwork.lean`**: Defines the base structure for a general neural network.
- **`Basic.lean`**, **`aux.lean`**, **`TSAux.lean`**: Contain auxiliary definitions and lemmas.

For more details, see the API documentation in `NeuralNetwork/README.md` and the source files.

## Installation
Installing Lean can be done by following the [leanprover community website](https://leanprover-community.github.io/get_started.html).
Our project uses Lean version 4.22.0.

This repository can then be cloned by following the instructions on [this page](https://leanprover-community.github.io/install/project.html).

## License
See LICENSE.md
