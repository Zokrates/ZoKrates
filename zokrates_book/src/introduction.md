# Introduction

ZoKrates is a toolbox for zkSNARKs on Ethereum. It helps you use verifiable computation in your DApp, from the specification of your program in a high level language to generating proofs of computation to verifying those proofs in Solidity.


## Background on zkSNARKs

 Zero-knowledge proofs (ZKPs) are a family of probabilistic protocols, first described by [Goldwasser, Micali and Rackoff](http://people.csail.mit.edu/silvio/Selected%20Scientific%20Papers/Proof%20Systems/The_Knowledge_Complexity_Of_Interactive_Proof_Systems.pdf) in 1985.

One particular family of ZKPs is described as zero-knowledge **S**uccinct **N**on-interactive **AR**guments of **K**nowledge, a.k.a. zkSNARKs. zkSNARKs are the most widely used zero-knowledge protocols, with the anonymous cryptocurrency Zcash and the smart-contract platform Ethereum among the notable early adopters.

For further details we refer the reader to some introductory material provided by the community: [[1]](https://z.cash/technology/zksnarks/),[[2]](https://medium.com/@VitalikButerin/zkSNARKs-under-the-hood-b33151a013f6), [[3]](https://blog.decentriq.ch/zk-SNARKs-primer-part-one/).

## Motivation

Ethereum runs computations on all nodes of the network, resulting in high costs, limits in complexity, and low privacy. zkSNARKs have been enabling to only verify computations on-chain for a fraction of the cost of running them, but are hard to grasp and work with.

ZoKrates bridges this gap. It helps you create off-chain programs and link them to the Ethereum blockchain, expanding the possibilities for your DApp.

## License

ZoKrates is released under the GNU Lesser General Public License v3.