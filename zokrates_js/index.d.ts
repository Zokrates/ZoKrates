declare module 'zokrates-js' {

  export interface ResolverResult {
    source: string,
    location: string
  }

  export interface ComputationResult {
    witness: string,
    output: string
  }

  export interface CompilationArtifacts {
    program: Uint8Array,
    abi: string,
  }
  
  export interface SetupKeypair {
    vk: string,
    pk: Uint8Array,
  }

  export type AbiVersion = "v1" | "v2";
  export type ResolveCallback = (location: string, path: string) => ResolverResult;

  export interface ZoKratesProvider {
    compile(source: string, location: string, callback: ResolveCallback): CompilationArtifacts;
    setup(program: Uint8Array): SetupKeypair;
    computeWitness(artifacts: CompilationArtifacts, args: any[]): ComputationResult;
    exportSolidityVerifier(verifyingKey: string, abiVersion: AbiVersion): string;
    generateProof(program: Uint8Array, witness: string, provingKey: Uint8Array): string;
  }

  export function initialize(): Promise<ZoKratesProvider>;
}
