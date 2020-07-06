declare module 'zokrates-js' {

  export type G1Affine = [string, string];
  export type G2Affine = [G1Affine, G1Affine];
  export type ProvingKey = Uint8Array;

  export interface VerificationKey {
    alpha: G1Affine,
    beta: G2Affine,
    gamma: G2Affine,
    delta: G2Affine,
    gamma_abc: G1Affine[],
    raw: string,
  }

  export interface ProofPoints {
    a: G1Affine,
    b: G2Affine,
    c: G1Affine
  }

  export interface Proof {
    proof: ProofPoints,
    inputs: string[],
    raw: string
  }

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
    pk: ProvingKey,
    vk: VerificationKey
  }

  export type SolidityAbi = "v1" | "v2";
  export type ResolveCallback = (location: string, path: string) => ResolverResult;

  export interface ZoKratesProvider {
    compile(source: string, location: string, callback: ResolveCallback): CompilationArtifacts;
    setup(program: Uint8Array): SetupKeypair;
    computeWitness(artifacts: CompilationArtifacts, args: any[]): ComputationResult;
    exportSolidityVerifier(verifyingKey: VerificationKey, abi: SolidityAbi): string;
    generateProof(program: Uint8Array, witness: string, provingKey: Uint8Array): Proof;
  }

  export function initialize(): Promise<ZoKratesProvider>;
}
