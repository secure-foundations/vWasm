all:
	@echo 'Read the README.md file for what to do'

build:
	(cd .. && docker build -t 'vwasm-build-image:latest' .docker)

run:
	(cd .. && docker run --rm -it -v "$$(pwd):/vWasm" 'vwasm-build-image:latest' /bin/bash)

prebuilt: vwasm-build-image.tar.xz
	@echo "Loading prebuilt Docker image. This may take a minute or two."
	docker load -i $<

vwasm-build-image.tar.xz:
	@echo 'ERROR: Download $@ from https://github.com/secure-foundations/vWasm/releases/tag/docker-image into the current directory'
	@false

.PHONY: all run build prebuilt
