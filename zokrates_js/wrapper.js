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
            const createConfig = (config) => ({
                allow_unconstrained_variables: false,
                ...config
            });
            const { location = "main.zok", resolveCallback = () => null, config = {} } = options;
            const callback = (currentLocation, importLocation) => {
                return resolveFromStdlib(currentLocation, importLocation) || resolveCallback(currentLocation, importLocation);
            };
            const { program, abi } = zokrates.compile(source, location, callback, createConfig(config));
            return {
                program: new Uint8Array(program),
                abi
            }
        },
        setup: (program) => {
            const { vk, pk } = zokrates.setup(program);
            return {
                vk,
                pk: new Uint8Array(pk)
            };
        },
        computeWitness: (artifacts, args) => {
            const { program, abi } = artifacts;
            return zokrates.compute_witness(program, abi, JSON.stringify(Array.from(args)));
        },
        exportSolidityVerifier: (verificationKey, abiVersion) => {
            return zokrates.export_solidity_verifier(verificationKey, abiVersion);
        },
        generateProof: (program, witness, provingKey) => {
            return zokrates.generate_proof(program, witness, provingKey);
        },
        verify: (verificationKey, proof) => {
            return zokrates.verify(verificationKey, proof);
        }
    }
};