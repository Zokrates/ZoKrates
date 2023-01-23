import { inflate } from "pako";
import metadata from "./metadata.js";
import * as wasmExports from "./wasm.js";

const initialize = async () => {
  await wasmExports.init(inflate);

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

        const ptr = wasmExports.compile(source, location, resolveCallback, config, curve);
        const result = Object.assign(
          {
            program: ptr.program(),
            abi: ptr.abi(),
            constraintCount: ptr.constraint_count(),
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
        const ptr = wasmExports.compute_witness(
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
        return wasmExports.setup(program, options);
      },
      universalSetup: (curve, size) => {
        return wasmExports.universal_setup(curve, size);
      },
      setupWithSrs: (srs, program, options) => {
        return wasmExports.setup_with_srs(srs, program, options);
      },
      generateProof: (program, witness, provingKey, options) => {
        return wasmExports.generate_proof(program, witness, provingKey, options);
      },
      verify: (vk, proof, options) => {
        return wasmExports.verify(vk, proof, options);
      },
      exportSolidityVerifier: (vk) => {
        return wasmExports.export_solidity_verifier(vk);
      },
      utils: {
        formatProof: (proof) => {
          return wasmExports.format_proof(proof);
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

export { initialize, metadata };