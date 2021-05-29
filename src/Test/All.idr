module Test.All

import Test.Blockchain.Ethereum.HexString
import Test.Data.Natural
import Test.Data.Crypt.LFSR
import Test.Keccak
import Test.Keccak.Padding
import Test.Keccak.Permutation

export
testAll : IO ()
testAll = do
  Test.Blockchain.Ethereum.HexString.testAll
  Test.Data.Natural.testAll
  Test.Data.Crypt.LFSR.testAll
  Test.Keccak.testAll
  Test.Keccak.Padding.testAll
  Test.Keccak.Permutation.testAll
  pure ()
