// This file is MIT Licensed.
//
// Copyright 2017 Christian Reitwiessner
// Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
// The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

pragma solidity ^0.4.14;

library Pairing {
	struct G1Point {
		uint X;
		uint Y;
	}
	// Encoding of field elements is: X[0] * z + X[1]
	struct G2Point {
		uint[2] X;
		uint[2] Y;
	}
	/// @return the generator of G1
	function P1() internal returns (G1Point) {
		return G1Point(1, 2);
	}
	/// @return the generator of G2
	function P2() internal returns (G2Point) {
		return G2Point(
			[11559732032986387107991004021392285783925812861821192530917403151452391805634,
			 10857046999023057135944570762232829481370756359578518086990519993285655852781],
			[4082367875863433681332203403145435568316851327593401208105741076214120093531,
			 8495653923123431417604973247489272438418190587263600148770280649306958101930]
		);
	}
	/// @return the negation of p, i.e. p.add(p.negate()) should be zero.
	function negate(G1Point p) internal returns (G1Point) {
		// The prime q in the base field F_q for G1
		uint q = 21888242871839275222246405745257275088696311157297823662689037894645226208583;
		if (p.X == 0 && p.Y == 0)
			return G1Point(0, 0);
		return G1Point(p.X, q - (p.Y % q));
	}
	/// @return the sum of two points of G1
	function add(G1Point p1, G1Point p2) internal returns (G1Point r) {
		uint[4] memory input;
		input[0] = p1.X;
		input[1] = p1.Y;
		input[2] = p2.X;
		input[3] = p2.Y;
		bool success;
		assembly {
			success := call(sub(gas, 2000), 6, 0, input, 0xc0, r, 0x60)
			// Use "invalid" to make gas estimation work
			switch success case 0 { invalid }
		}
		require(success);
	}
	/// @return the product of a point on G1 and a scalar, i.e.
	/// p == p.mul(1) and p.add(p) == p.mul(2) for all points p.
	function mul(G1Point p, uint s) internal returns (G1Point r) {
		uint[3] memory input;
		input[0] = p.X;
		input[1] = p.Y;
		input[2] = s;
		bool success;
		assembly {
			success := call(sub(gas, 2000), 7, 0, input, 0x80, r, 0x60)
			// Use "invalid" to make gas estimation work
			switch success case 0 { invalid }
		}
		require (success);
	}
	/// @return the result of computing the pairing check
	/// e(p1[0], p2[0]) *  .... * e(p1[n], p2[n]) == 1
	/// For example pairing([P1(), P1().negate()], [P2(), P2()]) should
	/// return true.
	function pairing(G1Point[] p1, G2Point[] p2) internal returns (bool) {
		require(p1.length == p2.length);
		uint elements = p1.length;
		uint inputSize = elements * 6;
		uint[] memory input = new uint[](inputSize);
		for (uint i = 0; i < elements; i++)
		{
			input[i * 6 + 0] = p1[i].X;
			input[i * 6 + 1] = p1[i].Y;
			input[i * 6 + 2] = p2[i].X[0];
			input[i * 6 + 3] = p2[i].X[1];
			input[i * 6 + 4] = p2[i].Y[0];
			input[i * 6 + 5] = p2[i].Y[1];
		}
		uint[1] memory out;
		bool success;
		assembly {
			success := call(sub(gas, 2000), 8, 0, add(input, 0x20), mul(inputSize, 0x20), out, 0x20)
			// Use "invalid" to make gas estimation work
			switch success case 0 { invalid }
		}
		require(success);
		return out[0] != 0;
	}
	/// Convenience method for a pairing check for two pairs.
	function pairingProd2(G1Point a1, G2Point a2, G1Point b1, G2Point b2) internal returns (bool) {
		G1Point[] memory p1 = new G1Point[](2);
		G2Point[] memory p2 = new G2Point[](2);
		p1[0] = a1;
		p1[1] = b1;
		p2[0] = a2;
		p2[1] = b2;
		return pairing(p1, p2);
	}
	/// Convenience method for a pairing check for three pairs.
	function pairingProd3(
			G1Point a1, G2Point a2,
			G1Point b1, G2Point b2,
			G1Point c1, G2Point c2
	) internal returns (bool) {
		G1Point[] memory p1 = new G1Point[](3);
		G2Point[] memory p2 = new G2Point[](3);
		p1[0] = a1;
		p1[1] = b1;
		p1[2] = c1;
		p2[0] = a2;
		p2[1] = b2;
		p2[2] = c2;
		return pairing(p1, p2);
	}
	/// Convenience method for a pairing check for four pairs.
	function pairingProd4(
			G1Point a1, G2Point a2,
			G1Point b1, G2Point b2,
			G1Point c1, G2Point c2,
			G1Point d1, G2Point d2
	) internal returns (bool) {
		G1Point[] memory p1 = new G1Point[](4);
		G2Point[] memory p2 = new G2Point[](4);
		p1[0] = a1;
		p1[1] = b1;
		p1[2] = c1;
		p1[3] = d1;
		p2[0] = a2;
		p2[1] = b2;
		p2[2] = c2;
		p2[3] = d2;
		return pairing(p1, p2);
	}
}
contract Test {
	using Pairing for *;
	struct VerifyingKey {
		Pairing.G2Point A;
		Pairing.G1Point B;
		Pairing.G2Point C;
		Pairing.G2Point gamma;
		Pairing.G1Point gammaBeta1;
		Pairing.G2Point gammaBeta2;
		Pairing.G2Point Z;
		Pairing.G1Point[] IC;
	}
	struct Proof {
		Pairing.G1Point A;
		Pairing.G1Point A_p;
		Pairing.G2Point B;
		Pairing.G1Point B_p;
		Pairing.G1Point C;
		Pairing.G1Point C_p;
		Pairing.G1Point K;
		Pairing.G1Point H;
	}
	function f() returns (bool) {
		Pairing.G1Point memory p1;
		Pairing.G1Point memory p2;
		p1.X = 1; p1.Y = 2;
		p2.X = 1; p2.Y = 2;
		var explict_sum = Pairing.add(p1, p2);
		var scalar_prod = Pairing.mul(p1, 2);
		return (explict_sum.X == scalar_prod.X &&
				explict_sum.Y == scalar_prod.Y);
	}
	function g() returns (bool) {
		Pairing.G1Point memory x = Pairing.add(Pairing.P1(), Pairing.negate(Pairing.P1()));
		// should be zero
		return (x.X == 0 && x.Y == 0);
	}
	function testMul() returns (bool) {
		Pairing.G1Point memory p;
		// @TODO The points here are reported to be not well-formed
		p.X = 14125296762497065001182820090155008161146766663259912659363835465243039841726;
		p.Y = 16229134936871442251132173501211935676986397196799085184804749187146857848057;
		p = Pairing.mul(p, 13986731495506593864492662381614386532349950841221768152838255933892789078521);
		return
			p.X == 18256332256630856740336504687838346961237861778318632856900758565550522381207 &&
			p.Y == 6976682127058094634733239494758371323697222088503263230319702770853579280803;
	}
	function pair() returns (bool) {
		Pairing.G2Point memory fiveTimesP2 = Pairing.G2Point(
			[4540444681147253467785307942530223364530218361853237193970751657229138047649, 20954117799226682825035885491234530437475518021362091509513177301640194298072],
			[11631839690097995216017572651900167465857396346217730511548857041925508482915, 21508930868448350162258892668132814424284302804699005394342512102884055673846]
		);
		// The prime p in the base field F_p for G1
		uint p = 21888242871839275222246405745257275088696311157297823662689037894645226208583;
		Pairing.G1Point[] memory g1points = new Pairing.G1Point[](2);
		Pairing.G2Point[] memory g2points = new Pairing.G2Point[](2);
// 			// check e(5 P1, P2)e(-P1, 5 P2) == 1
		g1points[0] = Pairing.P1().mul(5);
		g1points[1] = Pairing.P1();
		g1points[1].Y = p - g1points[1].Y;
		g2points[0] = Pairing.P2();
		g2points[1] = fiveTimesP2;
		if (!Pairing.pairing(g1points, g2points))
			return false;
		// check e(P1, P2)e(-P1, P2) == 0
		g1points[0] = Pairing.P1();
		g1points[1] = Pairing.P1().negate();
		g2points[0] = Pairing.P2();
		g2points[1] = Pairing.P2();
		if (!Pairing.pairing(g1points, g2points))
			return false;
		return true;
	}
	function verifyingKey() internal returns (VerifyingKey vk) {
		vk.A = Pairing.G2Point([0x285a26e9b197d676628ad045d18390e8a7ce388a5fa13511c01414a79a929fac, 0x25568d893a33431a915aedd052ab43c993c10ef309666ab0a9dde322c8fc4dd], [0x2bba33dbe730f28f077574170251b169b2e8a97c81c99728d386001c3273177e, 0x6ca111a907089cc7245de40c18a1c1cb594557cf72b3e9f2708e92f3219aa3]);
		vk.B = Pairing.G1Point(0xb6eaa484d5455aa6ba0d960993d6a8c9b4fbdacf90a09ac60795a687c4a831d, 0x1664ac93e8d962d0770df40cf566f85e928747ac86a9c5986b3c71d83b1b1f80);
		vk.C = Pairing.G2Point([0xd86d0c9deb3ddbc98f9564842fd1ab00dde80f81f039a0a4e3ebfb4ee3c61d3, 0x1fe9f6cc6757e462eaba04800bef3b9b8c1ca522bad2c7be134613fc510aa71], [0x22f4986476a8c9d8c2a3f7ccecc114e730944ce07f200478e6e0f1db2de03eae, 0x27e2acc664f790e44e2ae0fcd317a32113b81380f5dd5c0267a86456785b4138]);
		vk.gamma = Pairing.G2Point([0x1f6641c57a44524d2fa682fbd1934bbd998d9e3135fa7ea149967a1e819a26e7, 0x1534534b7de12e217b7bf94199690ec0a2f1ad039dd0900d96129aa17f399349], [0xfb45d72c76941d5fb7ee0e8100b16688b19f67578ef6dab619b8d00e1a8178f, 0xc794ea6fab1dce542b4b79839fb1c5c35b1b66904019dacddcef4ad67bed1f4]);
		vk.gammaBeta1 = Pairing.G1Point(0x1cdf6a78e07456eafad1ccbef857a917b149b00415dc60f1189368e8a06ee929, 0x1236028fe3a16daa9637115572bbe1c03ca00b4eddbe365108b8fba4bafa4e7e);
		vk.gammaBeta2 = Pairing.G2Point([0x24b7ad0a90a949d0fc805996e030a2699c290d6663ab3249a317b11eef79351b, 0x1c49678094077392427123479295c2ef7fe59ba5241006d6a43d6a2aae545553], [0x12ec2921e75b45877908aa68666922a460b6576ee44f8413c1c610135f70fd0, 0x1d125d05606dd98e6641b16d2e67563894668bf1fcda63e31c2f3ecf949ac10c]);
		vk.Z = Pairing.G2Point([0xe8acafd8ddcbc126023c5bec87e0f3d0d80cc8b59862450b998ca9ef2f86735, 0x1f280405aa6eea11a41a055a331dd04db1927df4a952adba0cbc8e866a590af5], [0xd5616140e7d667c9ff1a301880b812b732e976022fe815b40867a932b78329c, 0x505884a3ad3f5303a9c21a979598cc471e894de269de08f2232fb63c0d08663]);
		vk.IC = new Pairing.G1Point[](4);
		vk.IC[0] = Pairing.G1Point(0x1ceb4df15dbf096459bced8171ac25759873381e50a0d28229e10c2eb2ac164, 0xc092fd6678dc34a27ef4d072e5d68b539ad0c3af8e82237dbddf5be395f3ff4);
		vk.IC[1] = Pairing.G1Point(0x1b87616a77ee79b638660220ae38176c1fe3f6e9c52f602c11afbe947f1d8cc, 0x12ad36de0d0e9f4595b3cba58e1dbbf3c1028a745e85cef0d4d7bc70eab3724b);
		vk.IC[2] = Pairing.G1Point(0x1cd5faef1edeb2176b70e522e555a095098e510c96ca9fbdd6dda7118286a561, 0xf634248d72e916eb88f5947426cec1e8fa9755541a9f52f327ad93532702162);
		vk.IC[3] = Pairing.G1Point(0x14a9fb20ab0500c18eb9808a726736979bd7332ae5f338376c44271da7bc2857, 0x1db1417671b8a9f2852a2e2e56c9f3ce4902fce0155821fb6e20af7ea1a7ded7);
	}
	function verify(uint[] input, Proof proof) internal returns (uint) {
		VerifyingKey memory vk = verifyingKey();
		require(input.length + 1 == vk.IC.length);
		// Compute the linear combination vk_x
		Pairing.G1Point memory vk_x = Pairing.G1Point(0, 0);
		for (uint i = 0; i < input.length; i++)
			vk_x = Pairing.add(vk_x, Pairing.mul(vk.IC[i + 1], input[i]));
		vk_x = Pairing.add(vk_x, vk.IC[0]);
		if (!Pairing.pairingProd2(proof.A, vk.A, Pairing.negate(proof.A_p), Pairing.P2())) return 1;
		if (!Pairing.pairingProd2(vk.B, proof.B, Pairing.negate(proof.B_p), Pairing.P2())) return 2;
		if (!Pairing.pairingProd2(proof.C, vk.C, Pairing.negate(proof.C_p), Pairing.P2())) return 3;
		if (!Pairing.pairingProd3(
			proof.K, vk.gamma,
			Pairing.negate(Pairing.add(vk_x, Pairing.add(proof.A, proof.C))), vk.gammaBeta2,
			Pairing.negate(vk.gammaBeta1), proof.B
		)) return 4;
		if (!Pairing.pairingProd3(
				Pairing.add(vk_x, proof.A), proof.B,
				Pairing.negate(proof.H), vk.Z,
				Pairing.negate(proof.C), Pairing.P2()
		)) return 5;
		return 0;
	}
	event Verified(string);
	function verifyTx() returns (bool r) {
		uint[] memory input = new uint[](3);
		Proof memory proof;
		proof.A = Pairing.G1Point(0x1f99db87588a121f7613e9a374d19f26ab5904486b6cafab3c8b7f30840a5048, 0x2c8aca2feac69d83c4cdd7cf783feddda534e15fb4072cf91c2424b8e0051df1);
		proof.A_p = Pairing.G1Point(0x22f07b022291d58930cc4e366b2310590217801210f203dfa6a37ccb969be372, 0x24b17d39b866b4efcb58af749b66a60019430c29a2721db183bf3e758caef040);
		proof.B = Pairing.G2Point([0x2261b115ddcf079d133ad9c469192ed7df6ccbef0a83fb94d6c47d58f3ba59e9, 0x1d44b9bd9f5ed183546b65b1446f8bb4ac92309a97e28bf486a7be6b0be1c66e], [0x210ce9e2b07916f8e05333afae8bf4c29d916b73a4a0b6aa6d96db8ce9838245, 0x4825cffa3d725d46062251c59fe55b82987bc5ebbaa5f9f7e1eff2e00ea592c]);
		proof.B_p = Pairing.G1Point(0x2c144534c7afdcb40a1565159d64664130fc292daf3bd7a0cfa2616a8947d281, 0x11d2dc1e044023ec361b1f3bbd59b1e07d98468efe34279995aa35e0941fe741);
		proof.C = Pairing.G1Point(0x60049139c7256648ea7596fece8006cee1fbaaa54ba9977a54dad9dd4754d0b, 0xd7f5c78d61bf84ce0c1b7e1472022adfb28053d361c333a469dce8ca1e9a8ad);
		proof.C_p = Pairing.G1Point(0x1439f5149b482dd00f3493310fba8131a4ba6eb9bd857783027734b4e2403f13, 0x1f0ef9fd91c07a893f2739279039ec464c1323ff92e0055a1e001e643ee4605c);
		proof.H = Pairing.G1Point(0x130c4e9648ffaf4d0470532e1e690110798a457e08a669a04a621892b7ff6ae2, 0x18c2801082bc5050a53446b381535a21b1ab89841933822094122c68d82b8508);
		proof.K = Pairing.G1Point(0x2db627fe36d347ebb38c4f18af555f1d07f77ebcc4ddf4f5a80a8acbcf77d59d, 0x5c49dae6123e59fcaa6197f3e90d444745fe602ae57229f679fccbea7825ddb);
		input[0] = 1;
		input[1] = 1;
		input[2] = 2;
		if (verify(input, proof) == 0) {
		    Verified("Transaction successfully verified.");
		    return true;
		} else {
		    return false;
		}
	}
}
