var fs = require("fs");
let Web3 = require('web3');
const solc = require('solc');
const contractPath = process.argv[2]
const proofPath = process.argv[3]
const format = process.argv[4]
const web3 = new Web3(new Web3.providers.HttpProvider('http://localhost:8545'));

const source = fs.readFileSync(contractPath, 'UTF-8');
let jsonContractSource = {
    language: 'Solidity',
    sources: {
        [contractPath]: {
            content: source,
        },
    },
    settings: {
        optimizer: {
          enabled: true
        },
        outputSelection: {
            [contractPath]: {
                "Verifier": ['abi', "evm.bytecode"],
            },
        },
    },
};

(async () => {
    const accounts = await web3.eth.getAccounts();

    // The BN256G2 library needs to be deployed and linked separately
    // because it has `public` functions.
    // This is not needed for the Pairing library because all its functions
    // are `internal` and therefore are compiled into the contract that uses it.
    if (format == "gm17") {
        let library = await deployLibrary();
        jsonContractSource.settings.libraries = {
          [contractPath]: {
            BN256G2: library["_address"]
          }
        }
    }

    // -----Compile contract-----
    let jsonInterface = JSON.parse(solc.compile(JSON.stringify(jsonContractSource)));
    console.log(jsonInterface);

    let abi = jsonInterface.contracts[contractPath]["Verifier"].abi;
    let bytecode = jsonInterface.contracts[contractPath]["Verifier"].evm.bytecode;

    let contract = new web3.eth.Contract(abi)
        .deploy({
            data: '0x' + bytecode.object
        })
        .send({
            from: accounts[0],
            gas: '20000000'
        })
        .on('receipt', (tx) => {
            if (tx.status == true) {
                console.log("Contract Deployed! Gas used: " + tx.gasUsed);
            }
        })
        .then(newContractInstance => {
            contract = newContractInstance;
            Promise.all([makeTransaction(accounts[0], true)]);
        })
        .catch(err => {
            console.log(err);
            process.exit(1);
        });

    function makeTransaction(account, correct) {
        let proof = getProof(correct);

        function handleReceipt(tx) {
            if (tx.status == true && !correct) {
                console.log("Verification has been successful with invalid proof data! THIS IS A BUG");
                process.exit(1);
            }

            if (tx.status == true) {
                console.log("Correct proof works! Gas used: " + tx.gasUsed);
            }
        }

        function handleError(err, correct) {
            if (!correct) {
                console.log("False proof not verified! Success");
            } else {
                console.log(err);
                process.exit(1);
            }
        }

        console.log("PROOF:", proof)

        verifyTx(proof, account, correct).on('receipt', handleReceipt)
            .catch(handleError);
    }

    function verifyTx(proof, account, correct) {
        var args = proof[0];
        args = proof[1].length > 0 ? [args, proof[1]] : [args];

        console.log(args);

        return contract.methods.verifyTx(...args).send({
            from: account,
            gas: '20000000'
        });
    }

    function getProof(correct) {
        let json = JSON.parse(fs.readFileSync(proofPath));
        let inputs = json["inputs"];
        let proof = json["proof"];
        //falsifies proof to check if verification fails
        if (!correct) {
            proof["a"][0] = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        }
        return [Object.values(proof), Object.values(inputs)];
    }

    //function used for deploying BN256G2 Library, used for gm17 only
    function deployLibrary() {
        let jsonContractSourceBin = JSON.stringify({
            language: 'Solidity',
            sources: {
                ["BN256G2"]: {
                    content: source,
                },
            },
            settings: {
                optimizer: {
                  enabled: true
                },
                outputSelection: {
                    '*': {
                        '*': ['abi', "evm.bytecode"],
                    },
                },
            },
        });
        let jsonInterfaceBin = JSON.parse(solc.compile(jsonContractSourceBin));
        let abiLib = jsonInterfaceBin.contracts["BN256G2"]["BN256G2"].abi;
        let bytecodeLib = jsonInterfaceBin.contracts["BN256G2"]['BN256G2'].evm.bytecode;
        return new web3.eth.Contract(abiLib)
            .deploy({
                data: '0x' + bytecodeLib.object
            })
            .send({
                from: accounts[0],
                gas: '2000000'
            })
            .on('receipt', (tx) => {
                if (tx.status == false) {
                    console.log("Library couldn't be deployed");
                    process.exit(1);
                }
            });
    }
})();