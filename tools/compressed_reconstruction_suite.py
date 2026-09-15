"""Run the existing source-only suite with its verified compressed report reader."""
from compressed_reconstruction import compressed_storage
from reconstruction_suite import main


if __name__ == '__main__':
    with compressed_storage():
        raise SystemExit(main())
