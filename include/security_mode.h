#ifndef SECURITY_MODE_H
#define SECURITY_MODE_H

/* Security mode selection for capabilities. */

/* Operational modes for capability endpoints. */
enum security_mode {
    SEC_MODE_FAST = 0,
    SEC_MODE_HARDENED,
    SEC_MODE_PARANOID
};

/* Set the operating mode of a capability endpoint. */
void cap_set_security_mode(int cap_endpoint, enum security_mode mode);

#endif /* SECURITY_MODE_H */
