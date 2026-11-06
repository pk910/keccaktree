package io.github.pk910.keccaktree;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.nio.ByteBuffer;
import java.util.Arrays;
import org.bouncycastle.crypto.digests.KeccakDigest;
import org.junit.jupiter.api.Test;

/**
 * Every kernel this CPU supports, checked against BouncyCastle's
 * Keccak-256 for 0..300 nodes, offsets, in-place use and direct buffers.
 */
class KeccaktreeTest {
    static byte[] input(int nodes, int offset) {
        byte[] v = new byte[nodes * 64 + offset];
        int x = 0x9e3779b9 ^ nodes;
        for (int i = 0; i < v.length; i++) {
            x ^= x << 13;
            x ^= x >>> 17;
            x ^= x << 5;
            v[i] = (byte) x;
        }
        return v;
    }

    static byte[] reference(byte[] in, int offset, int nodes) {
        byte[] out = new byte[nodes * 32];
        KeccakDigest d = new KeccakDigest(256);
        for (int n = 0; n < nodes; n++) {
            d.update(in, offset + 64 * n, 64);
            d.doFinal(out, 32 * n);
        }
        return out;
    }

    static String hex(byte[] b) {
        StringBuilder s = new StringBuilder();
        for (byte x : b) s.append(String.format("%02x", x & 0xff));
        return s.toString();
    }

    @Test
    void knownVector() {
        assertEquals("ad3228b676f7d3cd4284a5443f17f1962b36e491b30a40b2405849e597ba5fb5",
                hex(Keccaktree.hash(new byte[64])));
    }

    @Test
    void everyKernelMatchesReference() {
        System.out.println("platform " + NativeLoader.platform() + ", kernels " + Keccaktree.kernels());
        assertEquals("generic", Keccaktree.kernels().get(0));
        assertTrue(Keccaktree.kernels().size() > 1 || !NativeLoader.platform().matches(".*-(amd64|arm64|riscv64)"),
                "no SIMD kernel available");
        for (String k : Keccaktree.kernels()) {
            for (int nodes = 0; nodes <= 300; nodes++) {
                for (int offset : new int[] {0, 1, 7}) {
                    byte[] in = input(nodes, offset);
                    byte[] out = new byte[nodes * 32 + offset];
                    Keccaktree.hash(k, out, offset, in, offset, nodes);
                    assertArrayEquals(reference(in, offset, nodes), Arrays.copyOfRange(out, offset, out.length),
                            k + " nodes=" + nodes + " offset=" + offset);
                }
            }
        }
    }

    @Test
    void dispatchInPlaceAndOverlap() {
        Keccaktree.init();
        for (int nodes : new int[] {0, 1, 2, 3, 5, 8, 17, 64, 255, 256}) {
            byte[] buf = input(nodes, 0);
            byte[] expect = reference(buf, 0, nodes);
            assertArrayEquals(expect, Keccaktree.hash(buf), "dispatch nodes=" + nodes);

            byte[] inPlace = buf.clone();
            Keccaktree.hashInPlace(inPlace, 0, nodes);
            assertArrayEquals(expect, Arrays.copyOf(inPlace, nodes * 32), "in place nodes=" + nodes);

            // output overlapping the input at a different offset
            byte[] shifted = new byte[buf.length + 64];
            System.arraycopy(buf, 0, shifted, 64, buf.length);
            Keccaktree.hash(shifted, 32, shifted, 64, nodes);
            assertArrayEquals(expect, Arrays.copyOfRange(shifted, 32, 32 + nodes * 32), "overlap nodes=" + nodes);
        }
    }

    @Test
    void directBuffers() {
        int nodes = 37;
        byte[] in = input(nodes, 0);
        ByteBuffer src = ByteBuffer.allocateDirect(in.length + 5);
        src.position(5);
        src.put(in);
        src.position(5);
        ByteBuffer dst = ByteBuffer.allocateDirect(nodes * 32 + 3);
        dst.position(3);
        Keccaktree.hash(dst, src, nodes);
        assertEquals(3, dst.position());
        byte[] out = new byte[nodes * 32];
        dst.get(out);
        assertArrayEquals(reference(in, 0, nodes), out);
    }

    @Test
    void boundsAreChecked() {
        assertThrows(IndexOutOfBoundsException.class, () -> Keccaktree.hash(new byte[31], 0, new byte[64], 0, 1));
        assertThrows(IndexOutOfBoundsException.class, () -> Keccaktree.hash(new byte[32], 0, new byte[64], 1, 1));
        assertThrows(IllegalArgumentException.class, () -> Keccaktree.hash(new byte[32], new byte[65]));
        assertThrows(IllegalArgumentException.class, () -> Keccaktree.hash("nope", new byte[32], 0, new byte[64], 0, 1));
        assertThrows(IllegalArgumentException.class,
                () -> Keccaktree.hash(ByteBuffer.allocate(32), ByteBuffer.allocateDirect(64), 1));
    }
}
