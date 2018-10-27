test: example.calc
	python3 ./parser.py  '-2*(2+3)/3+123-1'

debug: example.calc
	python3 -mpudb  ./parser.py '-2*(2+3)/3+123-1'

doctest:
	python3 -m doctest ./parser.py
