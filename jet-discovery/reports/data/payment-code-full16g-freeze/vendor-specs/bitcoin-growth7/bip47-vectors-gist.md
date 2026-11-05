##BIP47 Reusable Payment Codes Test Vectors

Results obtained upon implementing [BIP47](https://github.com/bitcoin/bips/blob/master/bip-0047.mediawiki "BIP47 Reusable Payment Codes"). Payment codes are calculated assuming v1 specification without use of BitMessage.

###Alice's wallet:

**Mnemonic (BIP39):** [response seminar brave tip suit recall often sound stick owner lottery motion]

**Raw entropy (BIP39):** b7b8706d714d9166e66e7ed5b3c61048

**BIP32 seed hex:** 64dca76abc9c6f0cf3d212d248c380c4622c8f93b2c425ec6a5567fd5db57e10d3e6f94a2f6af4ac2edb8998072aad92098db73558c323777abf5bd1082d970a

**Payment code: (M/47'/0'/0')**
PM8TJTLJbPRGxSbc8EJi42Wrr6QbNSaSSVJ5Y3E4pbCYiTHUskHg13935Ubb7q8tx9GVbh2UuRnBc3WSyJHhUrw8KhprKnn9eDznYGieTzFcwQRya4GA

**ECDH parameters: (M/47'/0'/0'/0)**

*a0*: 8d6a8ecd8ee5e0042ad0cb56e3a971c760b5145c3917a8e7beaf0ed92d7a520c

*A0*: 0353883a146a23f988e0f381a9507cbdb3e3130cd81b3ce26daf2af088724ce683

###Bob's wallet:

**Mnemonic (BIP39):** [reward upper indicate eight swift arch injury crystal super wrestle already dentist]

**Raw entropy (BIP39):** b8bde1cba37dbc161d09aad9bfc81c9d

**BIP32 seed hex:** 87eaaac5a539ab028df44d9110defbef3797ddb805ca309f61a69ff96dbaa7ab5b24038cf029edec5235d933110f0aea8aeecf939ed14fc20730bba71e4b1110

**Payment code: (M/47'/0'/0')**
PM8TJS2JxQ5ztXUpBBRnpTbcUXbUHy2T1abfrb3KkAAtMEGNbey4oumH7Hc578WgQJhPjBxteQ5GHHToTYHE3A1w6p7tU6KSoFmWBVbFGjKPisZDbP97

**ECDH parameters: (M/47'/0'/0'/0 - M/47'/0'/0'/9)**

*b0*: 04448fd1be0c9c13a5ca0b530e464b619dc091b299b98c5cab9978b32b4a1b8b

*B0*: 024ce8e3b04ea205ff49f529950616c3db615b1e37753858cc60c1ce64d17e2ad8

*b1*: 6bfa917e4c44349bfdf46346d389bf73a18cec6bc544ce9f337e14721f06107b

*B1*: 03e092e58581cf950ff9c8fc64395471733e13f97dedac0044ebd7d60ccc1eea4d

*b2*: 46d32fbee043d8ee176fe85a18da92557ee00b189b533fce2340e4745c4b7b8c

*B2*: 029b5f290ef2f98a0462ec691f5cc3ae939325f7577fcaf06cfc3b8fc249402156

*b3*: 4d3037cfd9479a082d3d56605c71cbf8f38dc088ba9f7a353951317c35e6c343

*B3*: 02094be7e0eef614056dd7c8958ffa7c6628c1dab6706f2f9f45b5cbd14811de44

*b4*: 97b94a9d173044b23b32f5ab64d905264622ecd3eafbe74ef986b45ff273bbba

*B4*: 031054b95b9bc5d2a62a79a58ecfe3af000595963ddc419c26dab75ee62e613842

*b5*: ce67e97abf4772d88385e66d9bf530ee66e07172d40219c62ee721ff1a0dca01

*B5*: 03dac6d8f74cacc7630106a1cfd68026c095d3d572f3ea088d9a078958f8593572

*b6*: ef049794ed2eef833d5466b3be6fe7676512aa302afcde0f88d6fcfe8c32cc09

*B6*: 02396351f38e5e46d9a270ad8ee221f250eb35a575e98805e94d11f45d763c4651

*b7*: d3ea8f780bed7ef2cd0e38c5d943639663236247c0a77c2c16d374e5a202455b

*B7*: 039d46e873827767565141574aecde8fb3b0b4250db9668c73ac742f8b72bca0d0

*b8*: efb86ca2a3bad69558c2f7c2a1e2d7008bf7511acad5c2cbf909b851eb77e8f3

*B8*: 038921acc0665fd4717eb87f81404b96f8cba66761c847ebea086703a6ae7b05bd

*b9*: 18bcf19b0b4148e59e2bba63414d7a8ead135a7c2f500ae7811125fb6f7ce941

*B9*: 03d51a06c6b48f067ff144d5acdfbe046efa2e83515012cf4990a89341c1440289

###Shared secrets:

*S0*: f5bb84706ee366052471e6139e6a9a969d586e5fe6471a9b96c3d8caefe86fef

*S1*: adfb9b18ee1c4460852806a8780802096d67a8c1766222598dc801076beb0b4d

*S2*: 79e860c3eb885723bb5a1d54e5cecb7df5dc33b1d56802906762622fa3c18ee5

*S3*: d8339a01189872988ed4bd5954518485edebf52762bf698b75800ac38e32816d

*S4*: 14c687bc1a01eb31e867e529fee73dd7540c51b9ff98f763adf1fc2f43f98e83

*S5*: 725a8e3e4f74a50ee901af6444fb035cb8841e0f022da2201b65bc138c6066a2

*S6*: 521bf140ed6fb5f1493a5164aafbd36d8a9e67696e7feb306611634f53aa9d1f

*S7*: 5f5ecc738095a6fb1ea47acda4996f1206d3b30448f233ef6ed27baf77e81e46

*S8*: 1e794128ac4c9837d7c3696bbc169a8ace40567dc262974206fcf581d56defb4

*S9*: fe36c27c62c99605d6cd7b63bf8d9fe85d753592b14744efca8be20a4d767c37

###The first 10 addresses used by Alice for sending to Bob are:

141fi7TY3h936vRUKh1qfUZr8rSBuYbVBK

12u3Uued2fuko2nY4SoSFGCoGLCBUGPkk6

1FsBVhT5dQutGwaPePTYMe5qvYqqjxyftc

1CZAmrbKL6fJ7wUxb99aETwXhcGeG3CpeA

1KQvRShk6NqPfpr4Ehd53XUhpemBXtJPTL

1KsLV2F47JAe6f8RtwzfqhjVa8mZEnTM7t

1DdK9TknVwvBrJe7urqFmaxEtGF2TMWxzD

16DpovNuhQJH7JUSZQFLBQgQYS4QB9Wy8e

17qK2RPGZMDcci2BLQ6Ry2PDGJErrNojT5

1GxfdfP286uE24qLZ9YRP3EWk2urqXgC4s

###Alice's notification transaction to Bob:

**Alice's notification address:** 1JDdmqFLhpzcUwPeinhJbUPw4Co3aWLyzW

**private key of input unassociated with Alice's payment code:** Kx983SRhAZpAhj7Aac1wUXMJ6XZeyJKqCxJJ49dxEbYCT4a1ozRD

**Alice's payment code payload:** 010002b85034fb08a8bfefd22848238257b252721454bbbfba2c3667f168837ea2cdad671af9f65904632e2dcc0c6ad314e11d53fc82fa4c4ea27a4a14eccecc478fee00000000000000000000000000

**Bob's notification address:** 1ChvUUvht2hUQufHBXF8NgLhW8SwE2ecGV

**Bob's notification address public key:** 024ce8e3b04ea205ff49f529950616c3db615b1e37753858cc60c1ce64d17e2ad8

**Outpoint of first UTXO in Alice's notification transaction to Bob:** 86f411ab1c8e70ae8a0795ab7a6757aea6e4d5ae1826fc7b8f00c597d500609c01000000

**Shared secret:** 736a25d9250238ad64ed5da03450c6a3f4f8f4dcdf0b58d1ed69029d76ead48d

**Blinding mask:** be6e7a4256cac6f4d4ed4639b8c39c4cb8bece40010908e70d17ea9d77b4dc57f1da36f2d6641ccb37cf2b9f3146686462e0fa3161ae74f88c0afd4e307adbd5

**Alice's payment code payload after blinding:** 010002063e4eb95e62791b06c50e1a3a942e1ecaaa9afbbeb324d16ae6821e091611fa96c0cf048f607fe51a0327f5e2528979311c78cb2de0d682c61e1180fc3d543b00000000000000000000000000

**Notification transaction to be pushed:** 010000000186f411ab1c8e70ae8a0795ab7a6757aea6e4d5ae1826fc7b8f00c597d500609c010000006b483045022100ac8c6dbc482c79e86c18928a8b364923c774bfdbd852059f6b3778f2319b59a7022029d7cc5724e2f41ab1fcfc0ba5a0d4f57ca76f72f19530ba97c860c70a6bf0a801210272d83d8a1fa323feab1c085157a0791b46eba34afb8bfbfaeb3a3fcc3f2c9ad8ffffffff0210270000000000001976a9148066a8e7ee82e5c5b9b7dc1765038340dc5420a988ac1027000000000000536a4c50010002063e4eb95e62791b06c50e1a3a942e1ecaaa9afbbeb324d16ae6821e091611fa96c0cf048f607fe51a0327f5e2528979311c78cb2de0d682c61e1180fc3d543b0000000000000000000000000000000000

**Notification transaction hash:** 9414f1681fb1255bd168a806254321a837008dd4480c02226063183deb100204
