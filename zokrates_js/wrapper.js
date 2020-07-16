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
    const extension = importLocation.slice((path.lastIndexOf(".") - 1 >>> 0) + 2);
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
        compile: (source, location, callback) => {
            let importCallback = (currentLocation, importLocation) => {
                return resolveFromStdlib(currentLocation, importLocation) || callback(currentLocation, importLocation);
            };
            const { program, abi } = zokrates.compile(source, location, importCallback);
            return {
                program: Array.from(program),
                abi
            }
        },
        setup: (program) => {
            const { vk, pk } = zokrates.setup(program);
            return {
                vk,
                pk: Array.from(pk)
            };
        },
        computeWitness: (artifacts, args) => {
            return zokrates.compute_witness(artifacts, JSON.stringify(Array.from(args)));
        },
        exportSolidityVerifier: (verificationKey, abiVersion) => {
            return zokrates.export_solidity_verifier(verificationKey, abiVersion);
        },
        generateProof: (program, witness, provingKey) => {
            return zokrates.generate_proof(program, witness, provingKey);
        }
    }
};