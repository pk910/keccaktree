package io.github.pk910.keccaktree;

import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * Batched keccak256 for Merkle trees (Java bindings of keccaktree).
 *
 * <p>Hashes many 64-byte nodes (two 32-byte children) per call with the
 * hand-written SIMD kernels of the native library, chosen for the CPU on
 * first use. Same contract as hashtree's {@code hashtree_hash}, with
 * Ethereum keccak256 (pad {@code 0x01}, not NIST SHA3-256):
 *
 * <pre>digest[i] = keccak256(input[64*i .. 64*i+64])</pre>
 *
 * <p>The native library is loaded from the jar (linux and windows x86-64,
 * linux and macOS aarch64), or from the file named by the system property
 * {@code keccaktree.native.path}, or as {@code keccaktree_jni} from
 * {@code java.library.path}.
 */
public final class Keccaktree {
    private static final String[] KERNELS;

    static {
        NativeLoader.load();
        KERNELS = nativeKernels();
    }

    private Keccaktree() {}

    /** Selects the kernel for this CPU now instead of on the first call. */
    public static void init() {
        nativeInit();
    }

    /**
     * Hashes every 64-byte node of {@code input} into consecutive 32-byte
     * digests at the start of {@code output}.
     */
    public static void hash(byte[] output, byte[] input) {
        if (input.length % 64 != 0) {
            throw new IllegalArgumentException("input length " + input.length + " is not a multiple of 64");
        }
        hash(output, 0, input, 0, input.length / 64);
    }

    /** Hashes every node of {@code input} into a new array of digests. */
    public static byte[] hash(byte[] input) {
        byte[] output = new byte[input.length / 2];
        hash(output, input);
        return output;
    }

    /**
     * Hashes {@code count} 64-byte nodes starting at {@code input[inOffset]}
     * into {@code count} 32-byte digests starting at
     * {@code output[outOffset]}. {@code output} and {@code input} may be the
     * same array; overlapping ranges must then start at the same offset
     * (in-place layer reduction).
     */
    public static void hash(byte[] output, int outOffset, byte[] input, int inOffset, int count) {
        hashWith(-1, output, outOffset, input, inOffset, count);
    }

    /**
     * Hashes {@code count} nodes of {@code buffer} from {@code offset} in
     * place: digest {@code i} overwrites bytes {@code offset+32*i ..
     * offset+32*i+32}.
     */
    public static void hashInPlace(byte[] buffer, int offset, int count) {
        hash(buffer, offset, buffer, offset, count);
    }

    /**
     * Hashes {@code count} nodes from the position of {@code input} into
     * {@code count} digests at the position of {@code output}. Both must be
     * direct buffers; their positions are not changed.
     */
    public static void hash(ByteBuffer output, ByteBuffer input, int count) {
        if (!output.isDirect() || !input.isDirect()) {
            throw new IllegalArgumentException("hash(ByteBuffer, ByteBuffer, int) needs direct buffers");
        }
        if (count < 0) {
            throw new IllegalArgumentException("negative count");
        }
        long need = 64L * count;
        if (input.remaining() < need) {
            throw new IndexOutOfBoundsException("input has " + input.remaining() + " bytes, " + count + " nodes need " + need);
        }
        if (output.remaining() < need / 2) {
            throw new IndexOutOfBoundsException("output has " + output.remaining() + " bytes, " + count + " digests need " + need / 2);
        }
        if (output.isReadOnly()) {
            throw new java.nio.ReadOnlyBufferException();
        }
        if (count > 0) {
            nativeHashDirect(output, output.position(), input, input.position(), count);
        }
    }

    /**
     * Names of the kernels this CPU can run ({@code generic} first), for
     * {@link #hash(String, byte[], int, byte[], int, int)}.
     */
    public static List<String> kernels() {
        List<String> names = new ArrayList<>();
        for (String k : KERNELS) {
            if (k != null) names.add(k);
        }
        return Collections.unmodifiableList(names);
    }

    /** Like {@link #hash(byte[], int, byte[], int, int)}, with one specific kernel. */
    public static void hash(String kernel, byte[] output, int outOffset, byte[] input, int inOffset, int count) {
        int id = kernel == null ? -1 : Arrays.asList(KERNELS).indexOf(kernel);
        if (id < 0) {
            throw new IllegalArgumentException("kernel " + kernel + " is not supported here, see kernels()");
        }
        hashWith(id, output, outOffset, input, inOffset, count);
    }

    private static void hashWith(int kernel, byte[] output, int outOffset, byte[] input, int inOffset, int count) {
        if (count < 0) {
            throw new IllegalArgumentException("negative count");
        }
        long inEnd = inOffset + 64L * count;
        long outEnd = outOffset + 32L * count;
        if (inOffset < 0 || inEnd > input.length) {
            throw new IndexOutOfBoundsException("input range " + inOffset + ".." + inEnd + " outside 0.." + input.length);
        }
        if (outOffset < 0 || outEnd > output.length) {
            throw new IndexOutOfBoundsException("output range " + outOffset + ".." + outEnd + " outside 0.." + output.length);
        }
        if (count == 0) {
            return;
        }
        if (output == input && outOffset != inOffset && outOffset < inEnd && inOffset < outEnd) {
            // the kernels only support exact in-place aliasing
            input = Arrays.copyOfRange(input, inOffset, (int) inEnd);
            inOffset = 0;
        }
        nativeHash(kernel, output, outOffset, input, inOffset, count);
    }

    private static native void nativeInit();

    private static native void nativeHash(int kernel, byte[] output, int outOffset, byte[] input, int inOffset, int count);

    private static native void nativeHashDirect(ByteBuffer output, int outOffset, ByteBuffer input, int inOffset, int count);

    private static native String[] nativeKernels();
}
