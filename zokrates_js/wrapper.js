const getAbsolutePath = (basePath, relativePath) => {
  if (relativePath[0] !== ".") {
    return relativePath;
  }
  var stack = basePath.split("/");
  var chunks = relativePath.split("/");
  stack.pop();

  for (var i = 0; i < chunks.length; i++) {
    if (chunks[i] == ".") {
      continue;
    } else if (chunks[i] == "..") {
      stack.pop();
    } else {
      stack.push(chunks[i]);
    }
  }
  return stack.join("/");
};

const getImportPath = (currentLocation, importLocation) => {
  let path = getAbsolutePath(currentLocation, importLocation);
  const extension = path.slice(((path.lastIndexOf(".") - 1) >>> 0) + 2);
  return extension ? path : path.concat(".zok");
};

module.exports = (dep) => {
  const { zokrates, stdlib } = dep;

  const resolveFromStdlib = (currentLocation, importLocation) => {
    let key = getImportPath(currentLocation, importLocation);
    let source = stdlib[key];
    return source ? { source, location: key } : null;
  };

  const defaultProvider = {
    compile: (source, compileOptions = {}) => {
      var {
        curve = "bn128",
        location = "main.zok",
        resolveCallback = () => null,
        config = {},
        snarkjs = false,
      } = compileOptions;

      config = { snarkjs, ...config };

      const callback = (currentLocation, importLocation) => {
        return (
          resolveFromStdlib(currentLocation, importLocation) ||
          resolveCallback(currentLocation, importLocation)
        );
      };
      const ptr = zokrates.compile(source, location, callback, config, curve);
      return Object.assign(
        {
          program: ptr.program(),
          abi: ptr.abi(),
        },
        snarkjs ? { snarkjs: { program: ptr.snarkjs_program() } } : {}
      );
    },
    computeWitness: (input, args, computeOptions = {}) => {
      const { program, abi } =
        input instanceof Uint8Array ? { program: input, abi: null } : input;

      const { snarkjs = false } = computeOptions;
      const ptr = zokrates.compute_witness(program, abi, JSON.stringify(args), {
        snarkjs: snarkjs,
      });

      return Object.assign(
        {
          witness: ptr.witness(),
          output: ptr.output(),
        },
        snarkjs
          ? {
              snarkjs: {
                witness: ptr.snarkjs_witness(),
              },
            }
          : {}
      );
    },
    setup: (program, options) => {
      return zokrates.setup(program, options);
    },
    universalSetup: (curve, size) => {
      return zokrates.universal_setup(curve, size);
    },
    setupWithSrs: (srs, program, options) => {
      return zokrates.setup_with_srs(srs, program, options);
    },
    generateProof: (program, witness, provingKey, options) => {
      return zokrates.generate_proof(program, witness, provingKey, options);
    },
    verify: (vk, proof) => {
      return zokrates.verify(vk, proof);
    },
    exportSolidityVerifier: (vk) => {
      return zokrates.export_solidity_verifier(vk);
    },
    utils: {
      formatProof: (proof) => {
        return zokrates.format_proof(proof);
      },
    },
  };

  const withOptions = (options) => {
    return {
      withOptions,
      compile: (source, compileOptions = {}) =>
        defaultProvider.compile(source, {
          ...compileOptions,
          curve: options.curve,
        }),
      computeWitness: (artifacts, args, computeOptions = {}) =>
        defaultProvider.computeWitness(artifacts, args, computeOptions),
      setup: (program) => defaultProvider.setup(program, options),
      universalSetup: (size) =>
        defaultProvider.universalSetup(options.curve, size),
      setupWithSrs: (srs, program) =>
        defaultProvider.setupWithSrs(srs, program, options),
      generateProof: (program, witness, provingKey) =>
        defaultProvider.generateProof(program, witness, provingKey, options),
      verify: (vk, proof) => defaultProvider.verify(vk, proof),
      exportSolidityVerifier: (vk) =>
        defaultProvider.exportSolidityVerifier(vk),
      utils: {
        formatProof: (proof) => defaultProvider.utils.formatProof(proof),
      },
    };
  };

  return {
    ...withOptions({ scheme: "g16", curve: "bn128" }),
  };
};
