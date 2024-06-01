#include <lean/lean.h>
#include <ctime>
#include <unistd.h>

extern "C" lean_obj_res get_current_epoch_seconds() {
    std::time_t epoch = std::time(0);
    return lean_io_result_mk_ok(lean_unsigned_to_nat(epoch));
}

extern "C" lean_obj_res get_current_epoch_time() {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    lean_object* tuple = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(tuple, 0, lean_unsigned_to_nat(ts.tv_sec));
    lean_ctor_set(tuple, 1, lean_unsigned_to_nat(ts.tv_nsec));
    return lean_io_result_mk_ok(tuple);
}

extern "C" lean_obj_res time_offset() {
    std::time_t gmt, rawtime = std::time(nullptr);
    struct tm *ptm;

    #if !defined(WIN32)
        struct tm gbuf;
        ptm = gmtime_r(&rawtime, &gbuf);
    #else
        ptm = gmtime(&rawtime);
    #endif

    ptm->tm_isdst = -1;
    gmt = std::mktime(ptm);

    return lean_io_result_mk_ok(lean_int_to_int(static_cast<int>(std::difftime(rawtime, gmt))));
}