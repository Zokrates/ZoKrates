module.exports = (pkg) => {
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

      const ptr = pkg.compile(source, location, resolveCallback, config, curve);
      const result = Object.assign(
        {
          program: ptr.program(),
          abi: ptr.abi(),
        },
        snarkjs ? { snarkjs: { program: ptr.snarkjs_program() } } : {}
      );
      ptr.free();
      return result;
    },
    computeWitness: (input, args, computeOptions = {}) => {
      const { program, abi } =
        input instanceof Uint8Array ? { program: input, abi: null } : input;

      const { snarkjs = false, logCallback = console.log } = computeOptions;
      const ptr = pkg.compute_witness(
        program,
        abi,
        JSON.stringify(args),
        {
          snarkjs: snarkjs,
        },
        logCallback
      );

      const result = Object.assign(
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

      ptr.free();
      return result;
    },
    setup: (program, options) => {
      return pkg.setup(program, options);
    },
    universalSetup: (curve, size) => {
      return pkg.universal_setup(curve, size);
    },
    setupWithSrs: (srs, program, options) => {
      return pkg.setup_with_srs(srs, program, options);
    },
    generateProof: (program, witness, provingKey, options) => {
      return pkg.generate_proof(program, witness, provingKey, options);
    },
    verify: (vk, proof, options) => {
      return pkg.verify(vk, proof, options);
    },
    exportSolidityVerifier: (vk) => {
      return pkg.export_solidity_verifier(vk);
    },
    utils: {
      formatProof: (proof) => {
        return pkg.format_proof(proof);
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
      verify: (vk, proof) => defaultProvider.verify(vk, proof, options),
      exportSolidityVerifier: (vk) =>
        defaultProvider.exportSolidityVerifier(vk),
      utils: {
        formatProof: (proof) => defaultProvider.utils.formatProof(proof),
      },
    };
  };

  return {
    ...withOptions({ backend: "ark", scheme: "g16", curve: "bn128" }),
  };
};
