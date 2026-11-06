/* JNI glue for io.github.pk910.keccaktree.Keccaktree, linked against the
 * static library from lib/<platform>/libkeccaktree.a. Bounds are checked on
 * the Java side. */
#include <jni.h>
#include <string.h>
#include "keccaktree.h"
#if defined(__aarch64__) && defined(__linux__)
#include <sys/auxv.h>
#endif

#define JNI_FN(name) Java_io_github_pk910_keccaktree_Keccaktree_##name

/* Kernels that run on this CPU; index 0 is always generic. */
typedef struct {
    const char* name;
    keccaktree_hash_fcn fn;
} kernel;

static int cpu_supports(const char* name) {
#if defined(__x86_64__)
    __builtin_cpu_init();
    if (!strcmp(name, "avx2_x4") || !strcmp(name, "avx2_x8")) return __builtin_cpu_supports("avx2");
    if (!strcmp(name, "avx512vl_x4") || !strcmp(name, "avx512_x8"))
        return __builtin_cpu_supports("avx512f") && __builtin_cpu_supports("avx512vl");
#elif defined(__aarch64__) && defined(__APPLE__)
    (void)name; /* every Apple M-series core has FEAT_SHA3 */
#elif defined(__aarch64__) && defined(__linux__)
    if (!strncmp(name, "sha3_", 5)) return (getauxval(AT_HWCAP) & (1UL << 17)) != 0;
#endif
    return 1;
}

static const kernel kernels[] = {
    {"generic", keccaktree_keccak256_generic},
#ifdef __x86_64__
    {"avx2_x4", keccaktree_keccak256_avx2_x4},
    {"avx2_x8", keccaktree_keccak256_avx2_x8},
    {"avx512vl_x4", keccaktree_keccak256_avx512vl_x4},
    {"avx512_x8", keccaktree_keccak256_avx512_x8},
#endif
#ifdef __aarch64__
    {"neon_x2", keccaktree_keccak256_neon_x2},
    {"scalar_x1", keccaktree_keccak256_scalar_x1},
    {"sha3_x2", keccaktree_keccak256_sha3_x2},
    {"sha3_x3", keccaktree_keccak256_sha3_x3},
    {"sha3_x3r", keccaktree_keccak256_sha3_x3r},
#endif
};
#define NKERNELS ((int)(sizeof(kernels) / sizeof(kernels[0])))

static void hash_arrays(JNIEnv* env, keccaktree_hash_fcn fn, jbyteArray out, jint out_off, jbyteArray in,
                        jint in_off, jint count) {
    /* no other JNI calls are allowed inside the critical region */
    jboolean same = (*env)->IsSameObject(env, out, in);
    jbyte* o = (*env)->GetPrimitiveArrayCritical(env, out, NULL);
    if (!o) return;
    jbyte* i = same ? o : (*env)->GetPrimitiveArrayCritical(env, in, NULL);
    if (!i) {
        (*env)->ReleasePrimitiveArrayCritical(env, out, o, JNI_ABORT);
        return;
    }
    fn((unsigned char*)o + out_off, (const unsigned char*)i + in_off, (uint64_t)count);
    if (i != o) (*env)->ReleasePrimitiveArrayCritical(env, in, i, JNI_ABORT);
    (*env)->ReleasePrimitiveArrayCritical(env, out, o, 0);
}

JNIEXPORT void JNICALL JNI_FN(nativeInit)(JNIEnv* env, jclass cls) {
    (void)env, (void)cls;
    keccaktree_init(NULL);
}

JNIEXPORT void JNICALL JNI_FN(nativeHash)(JNIEnv* env, jclass cls, jint kernel_id, jbyteArray out, jint out_off,
                                          jbyteArray in, jint in_off, jint count) {
    (void)cls;
    hash_arrays(env, kernel_id < 0 ? keccaktree_hash : kernels[kernel_id].fn, out, out_off, in, in_off, count);
}

JNIEXPORT void JNICALL JNI_FN(nativeHashDirect)(JNIEnv* env, jclass cls, jobject out, jint out_off, jobject in,
                                                jint in_off, jint count) {
    (void)cls;
    unsigned char* o = (*env)->GetDirectBufferAddress(env, out);
    const unsigned char* i = (*env)->GetDirectBufferAddress(env, in);
    keccaktree_hash(o + out_off, i + in_off, (uint64_t)count);
}

JNIEXPORT jobjectArray JNICALL JNI_FN(nativeKernels)(JNIEnv* env, jclass cls) {
    (void)cls;
    jclass str = (*env)->FindClass(env, "java/lang/String");
    if (!str) return NULL;
    jobjectArray arr = (*env)->NewObjectArray(env, NKERNELS, str, NULL);
    if (!arr) return NULL;
    for (int k = 0; k < NKERNELS; k++) {
        /* unsupported kernels are reported as null, keeping the index */
        if (!cpu_supports(kernels[k].name)) continue;
        jstring s = (*env)->NewStringUTF(env, kernels[k].name);
        if (!s) return NULL;
        (*env)->SetObjectArrayElement(env, arr, k, s);
        (*env)->DeleteLocalRef(env, s);
    }
    return arr;
}
