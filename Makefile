test: example.calc
	python3 ./parser.py example.calc

debug: example.calc
	python3 -mpudb  ./parser.py example.calc

example.calc:
	echo 22+33 > example.calc

doctest:
	python3 -m doctest ./parser.py
