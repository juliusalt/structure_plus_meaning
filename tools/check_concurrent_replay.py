"""Execute every original replay result with proved concurrent stages."""
from parallel_packet_execution import main


if __name__ == "__main__":
    raise SystemExit(main(__file__, kind='replay', root='Concurrent_Replay_Execution'))
