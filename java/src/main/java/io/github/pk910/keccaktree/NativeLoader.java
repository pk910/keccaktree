package io.github.pk910.keccaktree;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Files;
import java.util.Locale;

/** Loads the keccaktree JNI library. */
final class NativeLoader {
    static final String PATH_PROPERTY = "keccaktree.native.path";
    private static final String NAME = "keccaktree_jni";

    private NativeLoader() {}

    static synchronized void load() {
        String path = System.getProperty(PATH_PROPERTY);
        if (path != null && !path.isEmpty()) {
            System.load(new File(path).getAbsolutePath());
            return;
        }
        String resource = "native/" + platform() + "/" + System.mapLibraryName(NAME);
        try (InputStream in = NativeLoader.class.getResourceAsStream(resource)) {
            if (in != null) {
                File tmp = File.createTempFile("keccaktree_jni", "-" + System.mapLibraryName(NAME));
                tmp.deleteOnExit();
                try (OutputStream out = Files.newOutputStream(tmp.toPath())) {
                    byte[] buf = new byte[1 << 16];
                    for (int n; (n = in.read(buf)) > 0; ) out.write(buf, 0, n);
                }
                System.load(tmp.getAbsolutePath());
                return;
            }
        } catch (IOException e) {
            throw new UnsatisfiedLinkError("keccaktree: cannot extract " + resource + ": " + e);
        }
        try {
            System.loadLibrary(NAME);
        } catch (UnsatisfiedLinkError e) {
            UnsatisfiedLinkError err = new UnsatisfiedLinkError("keccaktree: no native library for " + platform()
                    + " in the jar, in -D" + PATH_PROPERTY + " or on java.library.path");
            err.initCause(e);
            throw err;
        }
    }

    /** {@code <os>-<arch>}, matching the lib/ directory names. */
    static String platform() {
        String os = System.getProperty("os.name").toLowerCase(Locale.ROOT);
        String arch = System.getProperty("os.arch").toLowerCase(Locale.ROOT);
        String o = os.startsWith("linux") ? "linux"
                : os.startsWith("mac") || os.startsWith("darwin") ? "darwin"
                : os.startsWith("windows") ? "windows" : os.replaceAll("[^a-z0-9]", "");
        String a = arch.equals("amd64") || arch.equals("x86_64") ? "amd64"
                : arch.equals("aarch64") || arch.equals("arm64") ? "arm64" : arch;
        return o + "-" + a;
    }
}
