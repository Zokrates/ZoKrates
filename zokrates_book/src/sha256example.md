# Proving Knowledge of a Hash Pre-Image

Let’s jump into ZoKrates by working through a hands-on project together! This chapter introduces you to the basic features of ZoKrates and how to use zkSNARKs in a real-world example.

We’ll implement a problem that's very typical in blockchain use-cases: proving the knowledge of a pre-image for a given SHA-256 digest.

We will begin demystifying this machinery by computing the SHA-256 hash of the number `5`. Towards this end, we will navigate through multiple implementations of this hash function using different programming languages: Python (accessible and easy to debug), ZoKrates (to compile the zkSNARKs program) and Solidity (to close the loop with the Ethereum blockchain).

In the second part, we show how ZoKrates and the Ethereum blockchain can be used to allow a prover, let’s call her Peggy, to demonstrate beyond any reasonable doubt to a verifier, let’s call him Victor, that she knows a hash pre-image for a chosen digest by Victor, without revealing what the pre-image is.

## Pre-requisites

Make sure you have followed the instructions in the [Getting Started](gettingstarted.md) chapter and are able to run the "Hello World" example described there.

Note that you also need a working Python environment to reproduce the full tutorial. The Python section, however, is optional and for educational purpose only.  

## Python Implementation

We will start by implementing our example hash problem using Python.  

Have a look at the following Python code:

```py
import hashlib  

preimage = bytes.fromhex('00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00\
00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00 05')

bin(int(preimage.hex(), 16)) //binary representation of pre-image 
//output is '0b101'

hashlib.sha256(preimage).hexdigest() //compute hash
//output is
//'c6481e22c5ff4164af680b8cfaa5e8ed3120eeff89c4f307c4a6faaae059ce10'
```

Let's go through this example line-by-line.

Clearly, the first line imports the `hashlib` module which implements most of the common secure hash and message digest algorithms.  

Following this, we define our 512 bit pre-image using hexadecimal notation and assign the resulting byte object to the variable `preimage`. Please note that the input needs to be exactly 512 bits long, hence we have to left-pad the input with `00` hex values. Based on that, we arrive at the binary form of the pre-image:`'0b101'`. Since we use the default formatting options of the Python interpreter, the leading zeros are removed from the representation of the binary number in the console output.

Finally we compute the SHA-256 hex-digest for this pre-image which returns the following hex-string:
`'c6481e22c5ff4164af680b8cfaa5e8ed3120eeff89c4f307c4a6faaae059ce10'`

Calling `bin` we easily obtain a binary representation of the hash-digest.

```py
bin(0xc6481e22c5ff4164af680b8cfaa5e8ed3120eeff89c4f307c4a6faaae059ce10)
//out
//'0b1100011001001000000111100010001011000101111111110100000101100100101011110110100000001011100011001111101010100101111010001110110100110001001000001110111011111111100010011100010011110011000001111100010010100110111110101010101011100000010110011100111000010000'
```

In the following sections we will try to reproduce this result first using ZoKrates and then using Solidity.

## ZoKrates Implementation

The goal for this chapter is to run the same hash calculation in a zkSNARK using ZoKrates.

First, we create a new file named `hashexample.code` with the following content:

```zokrates
import "LIBSNARK/sha256" as sha256

def main() -> (field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field, field):
	o255, o254, o253, o252, o251, o250, o249, o248, o247, o246, o245, o244, o243, o242, o241, o240, o239, o238, o237, o236, o235, o234, o233, o232, o231, o230, o229, o228, o227, o226, o225, o224, o223, o222, o221, o220, o219, o218, o217, o216, o215, o214, o213, o212, o211, o210, o209, o208, o207, o206, o205, o204, o203, o202, o201, o200, o199, o198, o197, o196, o195, o194, o193, o192, o191, o190, o189, o188, o187, o186, o185, o184, o183, o182, o181, o180, o179, o178, o177, o176, o175, o174, o173, o172, o171, o170, o169, o168, o167, o166, o165, o164, o163, o162, o161, o160, o159, o158, o157, o156, o155, o154, o153, o152, o151, o150, o149, o148, o147, o146, o145, o144, o143, o142, o141, o140, o139, o138, o137, o136, o135, o134, o133, o132, o131, o130, o129, o128, o127, o126, o125, o124, o123, o122, o121, o120, o119, o118, o117, o116, o115, o114, o113, o112, o111, o110, o109, o108, o107, o106, o105, o104, o103, o102, o101, o100, o99, o98, o97, o96, o95, o94, o93, o92, o91, o90, o89, o88, o87, o86, o85, o84, o83, o82, o81, o80, o79, o78, o77, o76, o75, o74, o73, o72, o71, o70, o69, o68, o67, o66, o65, o64, o63, o62, o61, o60, o59, o58, o57, o56, o55, o54, o53, o52, o51, o50, o49, o48, o47, o46, o45, o44, o43, o42, o41, o40, o39, o38, o37, o36, o35, o34, o33, o32, o31, o30, o29, o28, o27, o26, o25, o24, o23, o22, o21, o20, o19, o18, o17, o16, o15, o14, o13, o12, o11, o10, o9, o8, o7, o6, o5, o4, o3, o2, o1, o0 = sha256(0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,1)
	return o255, o254, o253, o252, o251, o250, o249, o248, o247, o246, o245, o244, o243, o242, o241, o240, o239, o238, o237, o236, o235, o234, o233, o232, o231, o230, o229, o228, o227, o226, o225, o224, o223, o222, o221, o220, o219, o218, o217, o216, o215, o214, o213, o212, o211, o210, o209, o208, o207, o206, o205, o204, o203, o202, o201, o200, o199, o198, o197, o196, o195, o194, o193, o192, o191, o190, o189, o188, o187, o186, o185, o184, o183, o182, o181, o180, o179, o178, o177, o176, o175, o174, o173, o172, o171, o170, o169, o168, o167, o166, o165, o164, o163, o162, o161, o160, o159, o158, o157, o156, o155, o154, o153, o152, o151, o150, o149, o148, o147, o146, o145, o144, o143, o142, o141, o140, o139, o138, o137, o136, o135, o134, o133, o132, o131, o130, o129, o128, o127, o126, o125, o124, o123, o122, o121, o120, o119, o118, o117, o116, o115, o114, o113, o112, o111, o110, o109, o108, o107, o106, o105, o104, o103, o102, o101, o100, o99, o98, o97, o96, o95, o94, o93, o92, o91, o90, o89, o88, o87, o86, o85, o84, o83, o82, o81, o80, o79, o78, o77, o76, o75, o74, o73, o72, o71, o70, o69, o68, o67, o66, o65, o64, o63, o62, o61, o60, o59, o58, o57, o56, o55, o54, o53, o52, o51, o50, o49, o48, o47, o46, o45, o44, o43, o42, o41, o40, o39, o38, o37, o36, o35, o34, o33, o32, o31, o30, o29, o28, o27, o26, o25, o24, o23, o22, o21, o20, o19, o18, o17, o16, o15, o14, o13, o12, o11, o10, o9, o8, o7, o6, o5, o4, o3, o2, o1, o0

```

Note that the `main` function does not take any input arguments. Having a closer look, the defined program is just calling the imported `sha256` function using 512 field elements, each one representing one bit of the input. Unsurprisingly, we set the input values to our pre-image, i.e. `5`, using the same binary encoding we derived above. In addition, we declare 256 field elements and set them to the output of the hash function. The last line defines the return statement for all these elements, i.e. the computed digest.

Having our problem described in ZoKrates' DSL, we can continue using ZoKrates for the rest of our workflow.

First, we compile the program into an arithmetic circuit using the `compile` command.

```sh
./zokrates compile -i hashexample.code
```

As a next step we can create a witness file using the following command:

```sh
./zokrates compute-witness
```

Note that the `-a` flag is not used in this case as we do not have to specify any public input argument for this program.  

Still here? Great! At this point, we can compare the created witness with the result obtained above.

Let's run the following bash magic in the console:

```sh
grep -r '~out_' witness | awk '{split($0,a,"out_"); print a[2]}' | sort -k1 -n | head -n 25 |  awk -F ' ' '{print $2}' | tr  -d '\n'  
```

which results in the following output:  
`1100011001001000000111100`

Recalling the 25 most significant bits of the hash digest obtained in the Python section

`1100011001001000000111100`

we can easily see that the two results are equivalent.

## Solidity Implementation

As a final step, we implement our example hash problem using Solidity and run the code on the test-net.

First, we create a new project using [Remix](https://remix.ethereum.org/) which works as a web IDE for Solidity development. Then, we create a new file named `hashexample.sol` with the following content:

```solidity
pragma solidity ^0.4.24;
contract SHA256Test {
    event Success(
        bytes32 indexed _id
    );

    function calc_sha() public returns (bytes32)  {
        bytes32 a = 0x0;
        bytes32 b = 0x5;

        bytes32 digest = sha256(a,b);
        emit Success(digest);
        return digest;
    }
}
```

Let's go over the main logic in that code: The function `calc_sha` takes two 32-byte long inputs, representing the total 512 bits described above, and calls the EVM opcode for SHA256. The result of the computation is stored in `digest`. In addition, the event `Success` is defined and  emitted with the computed digest as input.

Now, we can compile the contract and deploy it on your preferred Ethereum test-net. The next step is to call the public function `calc_sha` from the Remix UI.  

Following this the Remix console should show this event being logged:

`bytes32: 0xc6481e22c5ff4164af680b8cfaa5e8ed3120eeff89c4f307c4a6faaae059ce10`

Based on that result, the digest for our hash pre-image is the following hex-encoded 256-bit string:

`0xc6481e22c5ff4164af680b8cfaa5e8ed3120eeff89c4f307c4a6faaae059ce10`

Having this output we can compare it to the hash digest obtained in the Python and ZoKrates implementation. Clearly, we can state all three results are equivalent.  

## Prove knowledge of pre-image

At this point you might be wondering how all of this is useful. For now, we have seen that besides computing our hash in Python we can compute it using heavy finite field arithmetic on elliptic curves using ZoKrates as well as on the global state-machine Ethereum using Solidity.

Let's recall our goal: Peggy wants to proof that she knows a pre-image for a digest chosen by Victor, without revealing what the pre-image is. Without loss of generality, let's now assume that Victor choses the digest to be equivalent to our example above.  

To make it work, the two parties have to follow their roles in the protocol:


First, Victor has to specify what hash digest he is interested in. Therefore, we have to adjust the zkSNARK circuit, compiled by ZoKrates, such that in addition to computing the digest, it also validates it against the digest of interest, provided by Victor. This leads to the following update for `hashexample.code`:

```zokrates
import "LIBSNARK/sha256" as sha256

def main(private field i511, private field i510, private field i509, private field i508, private field i507, private field i506, private field i505, private field i504, private field i503, private field i502, private field i501, private field i500, private field i499, private field i498, private field i497, private field i496, private field i495, private field i494, private field i493, private field i492, private field i491, private field i490, private field i489, private field i488, private field i487, private field i486, private field i485, private field i484, private field i483, private field i482, private field i481, private field i480, private field i479, private field i478, private field i477, private field i476, private field i475, private field i474, private field i473, private field i472, private field i471, private field i470, private field i469, private field i468, private field i467, private field i466, private field i465, private field i464, private field i463, private field i462, private field i461, private field i460, private field i459, private field i458, private field i457, private field i456, private field i455, private field i454, private field i453, private field i452, private field i451, private field i450, private field i449, private field i448, private field i447, private field i446, private field i445, private field i444, private field i443, private field i442, private field i441, private field i440, private field i439, private field i438, private field i437, private field i436, private field i435, private field i434, private field i433, private field i432, private field i431, private field i430, private field i429, private field i428, private field i427, private field i426, private field i425, private field i424, private field i423, private field i422, private field i421, private field i420, private field i419, private field i418, private field i417, private field i416, private field i415, private field i414, private field i413, private field i412, private field i411, private field i410, private field i409, private field i408, private field i407, private field i406, private field i405, private field i404, private field i403, private field i402, private field i401, private field i400, private field i399, private field i398, private field i397, private field i396, private field i395, private field i394, private field i393, private field i392, private field i391, private field i390, private field i389, private field i388, private field i387, private field i386, private field i385, private field i384, private field i383, private field i382, private field i381, private field i380, private field i379, private field i378, private field i377, private field i376, private field i375, private field i374, private field i373, private field i372, private field i371, private field i370, private field i369, private field i368, private field i367, private field i366, private field i365, private field i364, private field i363, private field i362, private field i361, private field i360, private field i359, private field i358, private field i357, private field i356, private field i355, private field i354, private field i353, private field i352, private field i351, private field i350, private field i349, private field i348, private field i347, private field i346, private field i345, private field i344, private field i343, private field i342, private field i341, private field i340, private field i339, private field i338, private field i337, private field i336, private field i335, private field i334, private field i333, private field i332, private field i331, private field i330, private field i329, private field i328, private field i327, private field i326, private field i325, private field i324, private field i323, private field i322, private field i321, private field i320, private field i319, private field i318, private field i317, private field i316, private field i315, private field i314, private field i313, private field i312, private field i311, private field i310, private field i309, private field i308, private field i307, private field i306, private field i305, private field i304, private field i303, private field i302, private field i301, private field i300, private field i299, private field i298, private field i297, private field i296, private field i295, private field i294, private field i293, private field i292, private field i291, private field i290, private field i289, private field i288, private field i287, private field i286, private field i285, private field i284, private field i283, private field i282, private field i281, private field i280, private field i279, private field i278, private field i277, private field i276, private field i275, private field i274, private field i273, private field i272, private field i271, private field i270, private field i269, private field i268, private field i267, private field i266, private field i265, private field i264, private field i263, private field i262, private field i261, private field i260, private field i259, private field i258, private field i257, private field i256, private field i255, private field i254, private field i253, private field i252, private field i251, private field i250, private field i249, private field i248, private field i247, private field i246, private field i245, private field i244, private field i243, private field i242, private field i241, private field i240, private field i239, private field i238, private field i237, private field i236, private field i235, private field i234, private field i233, private field i232, private field i231, private field i230, private field i229, private field i228, private field i227, private field i226, private field i225, private field i224, private field i223, private field i222, private field i221, private field i220, private field i219, private field i218, private field i217, private field i216, private field i215, private field i214, private field i213, private field i212, private field i211, private field i210, private field i209, private field i208, private field i207, private field i206, private field i205, private field i204, private field i203, private field i202, private field i201, private field i200, private field i199, private field i198, private field i197, private field i196, private field i195, private field i194, private field i193, private field i192, private field i191, private field i190, private field i189, private field i188, private field i187, private field i186, private field i185, private field i184, private field i183, private field i182, private field i181, private field i180, private field i179, private field i178, private field i177, private field i176, private field i175, private field i174, private field i173, private field i172, private field i171, private field i170, private field i169, private field i168, private field i167, private field i166, private field i165, private field i164, private field i163, private field i162, private field i161, private field i160, private field i159, private field i158, private field i157, private field i156, private field i155, private field i154, private field i153, private field i152, private field i151, private field i150, private field i149, private field i148, private field i147, private field i146, private field i145, private field i144, private field i143, private field i142, private field i141, private field i140, private field i139, private field i138, private field i137, private field i136, private field i135, private field i134, private field i133, private field i132, private field i131, private field i130, private field i129, private field i128, private field i127, private field i126, private field i125, private field i124, private field i123, private field i122, private field i121, private field i120, private field i119, private field i118, private field i117, private field i116, private field i115, private field i114, private field i113, private field i112, private field i111, private field i110, private field i109, private field i108, private field i107, private field i106, private field i105, private field i104, private field i103, private field i102, private field i101, private field i100, private field i99, private field i98, private field i97, private field i96, private field i95, private field i94, private field i93, private field i92, private field i91, private field i90, private field i89, private field i88, private field i87, private field i86, private field i85, private field i84, private field i83, private field i82, private field i81, private field i80, private field i79, private field i78, private field i77, private field i76, private field i75, private field i74, private field i73, private field i72, private field i71, private field i70, private field i69, private field i68, private field i67, private field i66, private field i65, private field i64, private field i63, private field i62, private field i61, private field i60, private field i59, private field i58, private field i57, private field i56, private field i55, private field i54, private field i53, private field i52, private field i51, private field i50, private field i49, private field i48, private field i47, private field i46, private field i45, private field i44, private field i43, private field i42, private field i41, private field i40, private field i39, private field i38, private field i37, private field i36, private field i35, private field i34, private field i33, private field i32, private field i31, private field i30, private field i29, private field i28, private field i27, private field i26, private field i25, private field i24, private field i23, private field i22, private field i21, private field i20, private field i19, private field i18, private field i17, private field i16, private field i15, private field i14, private field i13, private field i12, private field i11, private field i10, private field i9, private field i8, private field i7, private field i6, private field i5, private field i4, private field i3, private field i2, private field i1, private field i0) -> (field):
	
	h255, h254, h253, h252, h251, h250, h249, h248, h247, h246, h245, h244, h243, h242, h241, h240, h239, h238, h237, h236, h235, h234, h233, h232, h231, h230, h229, h228, h227, h226, h225, h224, h223, h222, h221, h220, h219, h218, h217, h216, h215, h214, h213, h212, h211, h210, h209, h208, h207, h206, h205, h204, h203, h202, h201, h200, h199, h198, h197, h196, h195, h194, h193, h192, h191, h190, h189, h188, h187, h186, h185, h184, h183, h182, h181, h180, h179, h178, h177, h176, h175, h174, h173, h172, h171, h170, h169, h168, h167, h166, h165, h164, h163, h162, h161, h160, h159, h158, h157, h156, h155, h154, h153, h152, h151, h150, h149, h148, h147, h146, h145, h144, h143, h142, h141, h140, h139, h138, h137, h136, h135, h134, h133, h132, h131, h130, h129, h128, h127, h126, h125, h124, h123, h122, h121, h120, h119, h118, h117, h116, h115, h114, h113, h112, h111, h110, h109, h108, h107, h106, h105, h104, h103, h102, h101, h100, h99, h98, h97, h96, h95, h94, h93, h92, h91, h90, h89, h88, h87, h86, h85, h84, h83, h82, h81, h80, h79, h78, h77, h76, h75, h74, h73, h72, h71, h70, h69, h68, h67, h66, h65, h64, h63, h62, h61, h60, h59, h58, h57, h56, h55, h54, h53, h52, h51, h50, h49, h48, h47, h46, h45, h44, h43, h42, h41, h40, h39, h38, h37, h36, h35, h34, h33, h32, h31, h30, h29, h28, h27, h26, h25, h24, h23, h22, h21, h20, h19, h18, h17, h16, h15, h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3, h2, h1, h0 = sha256(i511, i510, i509, i508, i507, i506, i505, i504, i503, i502, i501, i500, i499, i498, i497, i496, i495, i494, i493, i492, i491, i490, i489, i488, i487, i486, i485, i484, i483, i482, i481, i480, i479, i478, i477, i476, i475, i474, i473, i472, i471, i470, i469, i468, i467, i466, i465, i464, i463, i462, i461, i460, i459, i458, i457, i456, i455, i454, i453, i452, i451, i450, i449, i448, i447, i446, i445, i444, i443, i442, i441, i440, i439, i438, i437, i436, i435, i434, i433, i432, i431, i430, i429, i428, i427, i426, i425, i424, i423, i422, i421, i420, i419, i418, i417, i416, i415, i414, i413, i412, i411, i410, i409, i408, i407, i406, i405, i404, i403, i402, i401, i400, i399, i398, i397, i396, i395, i394, i393, i392, i391, i390, i389, i388, i387, i386, i385, i384, i383, i382, i381, i380, i379, i378, i377, i376, i375, i374, i373, i372, i371, i370, i369, i368, i367, i366, i365, i364, i363, i362, i361, i360, i359, i358, i357, i356, i355, i354, i353, i352, i351, i350, i349, i348, i347, i346, i345, i344, i343, i342, i341, i340, i339, i338, i337, i336, i335, i334, i333, i332, i331, i330, i329, i328, i327, i326, i325, i324, i323, i322, i321, i320, i319, i318, i317, i316, i315, i314, i313, i312, i311, i310, i309, i308, i307, i306, i305, i304, i303, i302, i301, i300, i299, i298, i297, i296, i295, i294, i293, i292, i291, i290, i289, i288, i287, i286, i285, i284, i283, i282, i281, i280, i279, i278, i277, i276, i275, i274, i273, i272, i271, i270, i269, i268, i267, i266, i265, i264, i263, i262, i261, i260, i259, i258, i257, i256, i255, i254, i253, i252, i251, i250, i249, i248, i247, i246, i245, i244, i243, i242, i241, i240, i239, i238, i237, i236, i235, i234, i233, i232, i231, i230, i229, i228, i227, i226, i225, i224, i223, i222, i221, i220, i219, i218, i217, i216, i215, i214, i213, i212, i211, i210, i209, i208, i207, i206, i205, i204, i203, i202, i201, i200, i199, i198, i197, i196, i195, i194, i193, i192, i191, i190, i189, i188, i187, i186, i185, i184, i183, i182, i181, i180, i179, i178, i177, i176, i175, i174, i173, i172, i171, i170, i169, i168, i167, i166, i165, i164, i163, i162, i161, i160, i159, i158, i157, i156, i155, i154, i153, i152, i151, i150, i149, i148, i147, i146, i145, i144, i143, i142, i141, i140, i139, i138, i137, i136, i135, i134, i133, i132, i131, i130, i129, i128, i127, i126, i125, i124, i123, i122, i121, i120, i119, i118, i117, i116, i115, i114, i113, i112, i111, i110, i109, i108, i107, i106, i105, i104, i103, i102, i101, i100, i99, i98, i97, i96, i95, i94, i93, i92, i91, i90, i89, i88, i87, i86, i85, i84, i83, i82, i81, i80, i79, i78, i77, i76, i75, i74, i73, i72, i71, i70, i69, i68, i67, i66, i65, i64, i63, i62, i61, i60, i59, i58, i57, i56, i55, i54, i53, i52, i51, i50, i49, i48, i47, i46, i45, i44, i43, i42, i41, i40, i39, i38, i37, i36, i35, i34, i33, i32, i31, i30, i29, i28, i27, i26, i25, i24, i23, i22, i21, i20, i19, i18, i17, i16, i15, i14, i13, i12, i11, i10, i9, i8, i7, i6, i5, i4, i3, i2, i1, i0)

	h255 ==  0
	h254 ==  0
	h253 ==  0
	h252 ==  0
	h251 ==  1
	h250 ==  0
	h249 ==  0
	h248 ==  0
	h247 ==  0
	h246 ==  1
	h245 ==  1
	h244 ==  1
	h243 ==  0
	h242 ==  0
	h241 ==  1
	h240 ==  1
	h239 ==  1
	h238 ==  0
	h237 ==  0
	h236 ==  1
	h235 ==  1
	h234 ==  0
	h233 ==  1
	h232 ==  0
	h231 ==  0
	h230 ==  0
	h229 ==  0
	h228 ==  0
	h227 ==  0
	h226 ==  1
	h225 ==  1
	h224 ==  1
	h223 ==  0
	h222 ==  1
	h221 ==  0
	h220 ==  1
	h219 ==  0
	h218 ==  1
	h217 ==  0
	h216 ==  1
	h215 ==  0
	h214 ==  1
	h213 ==  0
	h212 ==  1
	h211 ==  1
	h210 ==  1
	h209 ==  1
	h208 ==  1
	h207 ==  0
	h206 ==  1
	h205 ==  1
	h204 ==  0
	h203 ==  0
	h202 ==  1
	h201 ==  0
	h200 ==  1
	h199 ==  0
	h198 ==  0
	h197 ==  1
	h196 ==  0
	h195 ==  0
	h194 ==  0
	h193 ==  1
	h192 ==  1
	h191 ==  1
	h190 ==  1
	h189 ==  1
	h188 ==  0
	h187 ==  0
	h186 ==  0
	h185 ==  0
	h184 ==  0
	h183 ==  1
	h182 ==  1
	h181 ==  0
	h180 ==  0
	h179 ==  1
	h178 ==  1
	h177 ==  1
	h176 ==  1
	h175 ==  0
	h174 ==  0
	h173 ==  1
	h172 ==  0
	h171 ==  0
	h170 ==  0
	h169 ==  1
	h168 ==  1
	h167 ==  1
	h166 ==  0
	h165 ==  0
	h164 ==  1
	h163 ==  0
	h162 ==  0
	h161 ==  0
	h160 ==  1
	h159 ==  1
	h158 ==  1
	h157 ==  1
	h156 ==  1
	h155 ==  1
	h154 ==  1
	h153 ==  1
	h152 ==  1
	h151 ==  0
	h150 ==  1
	h149 ==  1
	h148 ==  1
	h147 ==  0
	h146 ==  1
	h145 ==  1
	h144 ==  1
	h143 ==  0
	h142 ==  0
	h141 ==  0
	h140 ==  0
	h139 ==  0
	h138 ==  1
	h137 ==  0
	h136 ==  0
	h135 ==  1
	h134 ==  0
	h133 ==  0
	h132 ==  0
	h131 ==  1
	h130 ==  1
	h129 ==  0
	h128 ==  0
	h127 ==  1
	h126 ==  0
	h125 ==  1
	h124 ==  1
	h123 ==  0
	h122 ==  1
	h121 ==  1
	h120 ==  1
	h119 ==  0
	h118 ==  0
	h117 ==  0
	h116 ==  1
	h115 ==  0
	h114 ==  1
	h113 ==  1
	h112 ==  1
	h111 ==  1
	h110 ==  0
	h109 ==  1
	h108 ==  0
	h107 ==  0
	h106 ==  1
	h105 ==  0
	h104 ==  1
	h103 ==  0
	h102 ==  1
	h101 ==  0
	h100 ==  1
	h99 ==  1
	h98 ==  1
	h97 ==  1
	h96 ==  1
	h95 ==  0
	h94 ==  0
	h93 ==  1
	h92 ==  1
	h91 ==  0
	h90 ==  0
	h89 ==  0
	h88 ==  1
	h87 ==  1
	h86 ==  1
	h85 ==  0
	h84 ==  1
	h83 ==  0
	h82 ==  0
	h81 ==  0
	h80 ==  0
	h79 ==  0
	h78 ==  0
	h77 ==  0
	h76 ==  1
	h75 ==  0
	h74 ==  1
	h73 ==  1
	h72 ==  0
	h71 ==  1
	h70 ==  1
	h69 ==  1
	h68 ==  1
	h67 ==  0
	h66 ==  1
	h65 ==  0
	h64 ==  1
	h63 ==  0
	h62 ==  0
	h61 ==  1
	h60 ==  0
	h59 ==  0
	h58 ==  1
	h57 ==  1
	h56 ==  0
	h55 ==  1
	h54 ==  0
	h53 ==  0
	h52 ==  0
	h51 ==  0
	h50 ==  0
	h49 ==  1
	h48 ==  0
	h47 ==  1
	h46 ==  1
	h45 ==  1
	h44 ==  1
	h43 ==  1
	h42 ==  1
	h41 ==  1
	h40 ==  1
	h39 ==  1
	h38 ==  0
	h37 ==  1
	h36 ==  0
	h35 ==  0
	h34 ==  0
	h33 ==  1
	h32 ==  1
	h31 ==  0
	h30 ==  1
	h29 ==  0
	h28 ==  0
	h27 ==  0
	h26 ==  1
	h25 ==  0
	h24 ==  0
	h23 ==  0
	h22 ==  1
	h21 ==  1
	h20 ==  1
	h19 ==  1
	h18 ==  0
	h17 ==  0
	h16 ==  0
	h15 ==  0
	h14 ==  0
	h13 ==  0
	h12 ==  1
	h11 ==  0
	h10 ==  0
	h9 ==  1
	h8 ==  0
	h7 ==  0
	h6 ==  1
	h5 ==  1
	h4 ==  0
	h3 ==  0
	h2 ==  0
	h1 ==  1
	h0 == 1

	return 1
```

Note that we now have defined the main function to accept 512 private input arguments. These inputs are used to encode the secret pre-image for which to compute the digest.

In addition, we must compare the result bit by bit with the hard-coded correct solution defined by Victor. Clearly, this program only returns true if all of the computed bits are equivalent.

So, having defined the program Victor is now ready to compile the code:

```sh
./zokrates compile -i hashexample.code
```

Based on that Victor can run the setup phase and export the Solidity verifier smart contract:

```sh
./zokrates setup
./zokrates export-verifier
```

`setup` will create a `verifiation.key` file and a `proving.key` file. Victor must make the `proving.key` publicly available to Alice.

`export-verifier` creates a `verifier.sol` Solidity contract file that contains our verification key and a nifty function `verifyTx`. Victor deploys this smart contract to the Ethereum network.

Alice uses the `proving.key` to compute a witness to the problem:

```sh
./zokrates compute-witness -a 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1
```

Note that Alice now provides the correct pre-image as an argument to the program. However, these inputs are declared as private variables in the program  and don't leak to Victor due to the zero knowledge aspect of the protocol.

Finally, Alice can run the command to construct the proof:

```sh
./zokrates generate-proof
```

ZoKrates creates a file for the proof consisting of the eight variables that make up the zkSNARKs proof. The `verifyTx` function in the smart contract deployed by Victor accepts these eight values, along with an array of public inputs. The array of public inputs consists of:

* any parameters in the ZoKrates function, which do not contain the `private` keyword
* the return value(s) of the ZoKrates function

In the example we're considering, all inputs are private and there is a single return value of `1`, hence Alice has to define her public input array as follows: `[1]`  

Victor is continuously monitoring the verification smart contract for the `Verified` event, which is emitted upon successful verification of a transaction. As soon as he observes the event triggered by a transaction from Alice's public address, he can be sure that Alice has a valid pre-image for the SHA-256 digest he has put into the smart contract.

## Summary

At this point, you’ve successfully ran you first zkSNARK on the Ethereum blockchain! Congratulations!  

This project was a hands-on way to introduce you to ZoKrates and the workflow to develop dApps using zkSNARKs.  

Remember that in this example only two parties have been involved. This special case makes it easy to deal with zkSNARK's trust assumptions: only Vitor was interested in verifying the claim by Alice, hence he can trust his execution of the setup phase.

However, in more general use-cases there might be multiple parties interested in verifying the correctness of Alice's statement. For example, in the zero-knowledge based cryptocurrency Zcash every node needs to be able to validate the correctness of transactions. In order to generalize the setup phase to these multi-party use-cases a tricky process, commonly referred to as “trusted setup” or "ceremony" needs to be conducted.

Currently, ZoKrates doesn't provide support for these types of setups.