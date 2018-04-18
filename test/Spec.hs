import Lib

main :: IO ()
main = if dummy == 1 then print "test passed" else error "dummy should be 1"
