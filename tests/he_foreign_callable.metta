!(bind! &pow (py-atom math.pow))
!(assertEqual (&pow 2 3) 8.0)

!(bind! &math (py-atom math))
!(assertEqual ((py-dot &math floor) (py-dot &math pi)) 3)
