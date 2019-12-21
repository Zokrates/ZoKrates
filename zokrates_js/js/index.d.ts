declare module 'zokrates-js' {

  export interface ResolverResult {
    source: string,
    location: string
  }
  
  export interface SetupKeypair {
    vk: string,
    pk: Uint8Array,
  }

  export type ResolveCallback = (location: string, path: string) => ResolverResult;
  export interface ZoKratesProvider {
    compile(source: string, location: string, callback: ResolveCallback): Uint8Array;
    setup(program: Uint8Array): SetupKeypair;
    computeWitness(program: Uint8Array, args: string[]): string;
    exportSolidityVerifier(verifyingKey: string, isAbiv2: boolean): string
    generateProof(program: Uint8Array, witness: string, provingKey: Uint8Array): string;
  }

  export function initialize(): Promise<ZoKratesProvider>;
}