pragma solidity ^0.4.11;

	library Pairing {
		struct G1Point {
			uint X;
			uint Y;
			uint Z;
		}
		// Encoding of field elements is: X[0] * z + X[1]
		struct G2Point {
			uint[2] X;
			uint[2] Y;
			uint[2] Z;
		}

		/// @return the generator of G1
		function P1() internal returns (G1Point) {
			return G1Point(1, 2, 1);
		}

		/// @return the generator of G2
		function P2() internal returns (G2Point) {
			return G2Point(
				[11559732032986387107991004021392285783925812861821192530917403151452391805634,
				 10857046999023057135944570762232829481370756359578518086990519993285655852781],
				[4082367875863433681332203403145435568316851327593401208105741076214120093531,
				 8495653923123431417604973247489272438418190587263600148770280649306958101930],
				[uint(0), 1]
			);
		}

		function g1FromAffine(uint X, uint Y) internal returns (G1Point) {
			return G1Point(X, Y, 1);
		}

		function g2FromAffine(uint[2] X, uint[2] Y) internal returns (G2Point) {
			return G2Point(X, Y, [uint(0), 1]);
		}

		function negate(G1Point p) internal returns (G1Point) {
			// The prime q in the base field F_q for G1
			uint q = 21888242871839275222246405745257275088696311157297823662689037894645226208583;
			if (p.X == 0 && p.Y == 1 && p.Z == 0)
				return G1Point(0, 1, 0);
			if (p.Z != 1) throw;
			return G1Point(p.X, q - (p.Y % q), 1);
		}

		function add(G1Point p1, G1Point p2) internal returns (G1Point r) {
			uint[6] memory input;
			input[0] = p1.X;
			input[1] = p1.Y;
			input[2] = p1.Z;
			input[3] = p2.X;
			input[4] = p2.Y;
			input[5] = p2.Z;
			bool success;
			assembly {
				success := call(sub(gas, 2000), 0x20, 0, input, 0xc0, r, 0x60)
			}
			if (!success) throw;
		}

		function mul(G1Point p, uint s) internal returns (G1Point r) {
			uint[4] memory input;
			input[0] = s;
			input[1] = p.X;
			input[2] = p.Y;
			input[3] = p.Z;
			bool success;
			assembly {
				success := call(sub(gas, 2000), 0x21, 0, input, 0x80, r, 0x60)
			}
			if (!success) throw;
		}

		function pairing(G1Point[] p1, G2Point[] p2) internal returns (bool) {
			if (p1.length != p2.length) throw;
			uint inputSize = p1.length * 9;
			uint[] memory input = new uint[](inputSize);
			for (uint i = 0; i < p1.length; i++)
			{
				input[i * 9 + 0] = p1[i].X;
				input[i * 9 + 1] = p1[i].Y;
				input[i * 9 + 2] = p1[i].Z;
				input[i * 9 + 3] = p2[i].X[0];
				input[i * 9 + 4] = p2[i].X[1];
				input[i * 9 + 5] = p2[i].Y[0];
				input[i * 9 + 6] = p2[i].Y[1];
				input[i * 9 + 7] = p2[i].Z[0];
				input[i * 9 + 8] = p2[i].Z[1];
			}
			uint[1] memory out;
			bool success;
			assembly {
				success := call(sub(gas, 2000), 0x22, 0, add(input, 0x20), mul(inputSize, 0x20), out, 0x20)
			}
			if (!success) throw;
			return out[0] != 0;
		}
		function pairingProd2(G1Point a1, G2Point a2, G1Point b1, G2Point b2) internal returns (bool) {
			G1Point[] memory p1 = new G1Point[](2);
			G2Point[] memory p2 = new G2Point[](2);
			p1[0] = a1;
			p1[1] = b1;
			p2[0] = a2;
			p2[1] = b2;
			return pairing(p1, p2);
		}
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

		function verifyingKey() internal returns (VerifyingKey vk) {
			vk.A = Pairing.g2FromAffine([0xafebf402a5754ad2d70a543517cb3e2a89a08c56d779fc47b52f380f6bb251d, 0x19faaa0e0908e5b5a5849deb0aa6c39b291e3648fa42f8f4f0178f5cbf6bbc81], [0xdbbefd36cf5a1f1a05a7338da24374b55a26baa9b04460e26ac4bb25e649f58, 0x21d5c7e5ca1a4dc9eb481396bbb89194b1ad4b4ebe3d054294f02cadeffce954]);
			vk.B = Pairing.g1FromAffine(0x289d652ceea8776d11f578fc1dcc4126de746479da5128b7101aa3e181415422, 0x175f1728c36d4c5709a24fa77a5f26c3cb39a90ee7e9d5b235fc55c2254647f5);
			vk.C = Pairing.g2FromAffine([0x13dc8167107608e826579e3106aa23d2a7d43c487889eba1d51981eb1adaa93d, 0x281eb0b03eccdc46a512446dbf8e05a5d816b9114086964a3fb9e550075cb6f8], [0x2dec3bc5d2d5fee114951c633b52d4ce59b9082aa2c7163f114c2196505b5b28, 0x2a476f4be32668677bcda0db082c6ca4105654f1a4047b82ab5606fef5721081]);
			vk.gamma = Pairing.g2FromAffine([0x103941cc36b44e8898648025a144e8c955470130cc05c9f80a55124df305a115, 0x1d1c951a86b0aca3cc9ee7684d5ca05a481deda2730d37526b18b12684f28982], [0xfd3fcd0e84405d71cc7abf6917e583991a568e722f4cd61e4045eb961c6fcbf, 0x74db4419937c092a1c060732f977e532ba606e5553e1fb4afc3bbe768cc43ef]);
			vk.gammaBeta1 = Pairing.g1FromAffine(0x1a3e88429e8cb657d99a64053da8b321f1249ea9635d3680bf7a366db2b57087, 0x1efe45cf3a57825fb434c0b6778709fa795b506d37c6911028716529627956b5);
			vk.gammaBeta2 = Pairing.g2FromAffine([0x173bb1f2f798cb0b584142dd0743d9bd65cb2c0b7ad1fd8cdcb3754c4dbf0c7e, 0x1eedcd99d3dd98ea58060885026f482813785fc95e33bc657c2dc1bb9d64558c], [0x1e3a05ed9b68093de66fb70b1187ae8dc2cc9f3cd7aada1c189ad655a271d6fd, 0x23e9e14b758baa94292cb11450b055509f476d56722daf97febcd91a36914589]);
			vk.Z = Pairing.g2FromAffine([0x14b6c5b03b67fe3b84c06fe5eefab125428b2a5c9f5e70664ae1caa38c46be32, 0x1b0a4a66cd254bb3416efe77a682ae0c608a0c1daf134af4875cbe72ab4f7631], [0x20b70a914f914da5b602f8d05dbd949a52df41d5ff51ea7a37b31ec59ff090b0, 0x1a7961bcb7df701031ef74b79209288513278b11993d6c7cdd8b91fd594d18c8]);
			vk.IC = new Pairing.G1Point[](4);
			vk.IC[0] = Pairing.g1FromAffine(0x281c781b5098b6eec2c58457ac11ae7d8cb0e77342b5590984b3c2603b642e18, 0x213eecf8d81b21aa77b0493cd4edb12c7ec7130e2722942faa3c3ba15425a194);
			vk.IC[1] = Pairing.g1FromAffine(0xfe4db8024a7efab033d496ad416066a67d40d5dab84703e898d1694e571f9e9, 0x38d6f73b8b0ec9e06db8a4b31081816a72ee86da8ef0b7cc1519e63da0ab60f);
			vk.IC[2] = Pairing.g1FromAffine(0x20e1eb528fd165114bbe135bd881dee1199354c8d7076a572ba3b5b39fa41297, 0x1673751c4ab597ef94bfbe64c94aae27425314ce26cce9e2e30fd1992d07cb11);
			vk.IC[3] = Pairing.g1FromAffine(0x18ee9a29756add25f7cce42194278937079ed012f2fce0ab67aa00d9aa91068, 0xc398991818ed538b5e5c14ff5692cb9da1f355d42fbd185873bc04e9e3b66f1);

		}
		function verify(uint[] input, Proof proof) internal returns (uint) {
			VerifyingKey memory vk = verifyingKey();
			if (input.length + 1 != vk.IC.length) throw;
			// Compute the linear combination vk_x
			Pairing.G1Point memory vk_x = Pairing.G1Point(0, 1, 0);
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
		function verifyTx() returns (bool) {
			uint[] memory input = new uint[](3);
			Proof memory proof;
			proof.A = Pairing.g1FromAffine(0x293c526cf53ef175c1e9cb00031818e249385e0d8fc50bdaa9dfbbea6a5c850a, 0x10640de2d3f085c2cf70455afbb1cc284115650762468ccdb8fd831fb8a9bbac);
			proof.A_p = Pairing.g1FromAffine(0x23cc3df2aa3ad9a0f09274bcd1a33c6ee3a9803fe18c8c4ea67d0541205c306e, 0x5130a0f4759fd31c18ebd34ccf6eae4449882994e9ad04aa898c513360b7133);
			proof.B = Pairing.g2FromAffine([0x1100284ed85901a7502ffac04d51817df060f1da8f52a67d9a1245f3d862188b, 0xeba42bcfb26c858dbcd19308d5f752c65d21ff84cdadc1ae9335f6d91b2e40b], [0x192313f0c0c429d53f0bbc2d94e18c7bc4d882afcb16a7c4e41428bfe1f78af4, 0x2e757adea510776388b076577c09568cae4314cf7542715ce0c4e9247d77ce88]);
			proof.B_p = Pairing.g1FromAffine(0x30413f23145abc931b5a1d799ac96d6b645f44758c5c113554ecf6df16937094, 0x1f3d3211ae44cf078eeb98fbd23cf3d4a17fefab8fc16034bd5dcebb4deb2e34);
			proof.C = Pairing.g1FromAffine(0x1b3738c1dde9fabedb0fb5c79c3b120300904b09fc953205c402d9390b008d8f, 0xd7d5589b77396d4fdf212f51cc20032bc0bf97a51733bbdf98a01a76ebdc900);
			proof.C_p = Pairing.g1FromAffine(0x2e20b340df2e0f6da9a63e873a479a626acaee99a6256852738a628149c78701, 0x4fef2a2fe82b85f09c044285323b970736b34dfb16ab4080da2b2747c7b961e);
			proof.H = Pairing.g1FromAffine(0x25a3225593b0aee4fba525814fbb64f49c48b5b2273439e375e512ab6e4dd249, 0xe483d22cdb058fd2c5cf56f0498fb7b008ca40eadb3c621c05eb970fc870268);
			proof.K = Pairing.g1FromAffine(0x270b10bdbd3f0d653e27a40e03ecf84f987829b019755e0e6dcbdf1900f7c44c, 0x14ad7a7aede1ca8dfb207be5100b07bc170ad6ffefc7bf5368f8a07f66c052d6);
			input[0] = 1;
			input[1] = 1;
			input[2] = 2;
			return verify(input, proof) == 0;
		}

	}
