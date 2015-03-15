flags=-pkg ocamlgraph lib/callstrings.cmi lib/callstrings.cmx -I lib

kstrings:
	bapbuild $(flags) kstrings.plugin

astrings:
	bapbuild $(flags) astrings.plugin

csforest:
	bapbuild $(flags) csforest.plugin

clean:
	rm -r _build
