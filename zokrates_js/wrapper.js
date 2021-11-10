const getAbsolutePath = (basePath, relativePath) => {
    if (relativePath[0] !== '.') {
        return relativePath;
    }
    var stack = basePath.split('/');
    var chunks = relativePath.split('/');
    stack.pop();

    for (var i = 0; i < chunks.length; i++) {
        if (chunks[i] == '.') {
            continue;
        } else if (chunks[i] == '..') {
            stack.pop();
        } else {
            stack.push(chunks[i]);
        }
    }
    return stack.join('/');
}

const getImportPath = (currentLocation, importLocation) => {
    let path = getAbsolutePath(currentLocation, importLocation);
    const extension = path.slice((path.lastIndexOf(".") - 1 >>> 0) + 2);
    return extension ? path : path.concat('.zok');
}

module.exports = (dep) => {

    const { zokrates, stdlib } = dep;

    const resolveFromStdlib = (currentLocation, importLocation) => {
        let key = getImportPath(currentLocation, importLocation);
        let source = stdlib[key];
        return source ? { source, location: key } : null;
    }

    return {
        compile: (source, options = {}) => {
            const { curve = "bn128", location = "main.zok", resolveCallback = () => null, config = {} } = options;
            const callback = (currentLocation, importLocation) => {
                return resolveFromStdlib(currentLocation, importLocation) || resolveCallback(currentLocation, importLocation);
            };
            const { program, abi } = zokrates.compile(curve, source, location, callback, config);
            return {
                program: new Uint8Array(program),
                abi
            }
        },
        computeWitness: (artifacts, args) => {
            const { program, abi } = artifacts;
            return zokrates.compute_witness(program, abi, JSON.stringify(Array.from(args)));
        },
        bellman: {
            groth16: {
                setup: (program) => zokrates.bellman_groth16_setup(program),
                generateProof: (program, witness, provingKey) => zokrates.bellman_groth16_generate_proof(program, witness, provingKey),
                exportSolidityVerifier: (vk) => zokrates.bellman_groth16_export_solidity_verifier(vk),
                verify: (vk, proof, curve = "bn128") => zokrates.bellman_groth16_verify(vk, proof, curve)
            }
        },
        ark: {
            gm17: {
                setup: (program) => zokrates.ark_gm17_setup(program),
                generateProof: (program, witness, provingKey) => zokrates.ark_gm17_generate_proof(program, witness, provingKey),
                verify: (vk, proof, curve = "bn128") => zokrates.ark_gm17_verify(vk, proof, curve)
            },
            marlin: {
                setup: (srs, program) => zokrates.ark_marlin_setup(srs, program),
                universalSetup: (curve, size) => zokrates.ark_marlin_universal_setup(curve, size),
                generateProof: (program, witness, provingKey) => zokrates.ark_marlin_generate_proof(program, witness, provingKey),
                verify: (vk, proof, curve = "bn128") => zokrates.ark_marlin_verify(vk, proof, curve)
            }
        }
    }
};