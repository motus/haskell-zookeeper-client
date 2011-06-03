
import Zookeeper

main = do
  zh <- zInit "" zNullWatcher 10000  
  zClose zh
  where zNullWatcher zh zType zState path = putStrLn path


