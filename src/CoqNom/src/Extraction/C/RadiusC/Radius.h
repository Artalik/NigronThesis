#include "../Datatypes.h"

typedef struct RadiusAttribute {
    int key;
    union Attribute {
        struct { span v; } UserName;
        struct { span v; } UserPassword;
        struct { uint8_t n; span v; } ChapPassword;
        struct { ipv4 ip; } NasIPAddress;
        struct { uint32_t v; } NasPort;
        struct { uint32_t v; } Protocol;
        struct { ipv4 ip; } FramedIPAddress;
        struct { ipv4 ip; } FramedIPNetmask;
        struct { uint32_t v; } Routing;
        struct { span s; } FilterId;
        struct { uint32_t v; } FramedMTU;
        struct { uint32_t v; } Compression;
        struct { uint32_t v; span s; } VendorSpecific;
        struct { span s; } CalledStationId;
        struct { span s; } CallingStationId;
        struct { uint8_t n; span s; } Unknown;
        struct { uint32_t v; } Service;
    } attribute;
} radius_attribute;

DEFINE_VECTOR(radius_attribute);
DEFINE_OPTION(Vector_radius_attribute);
DEFINE_VECTOR(uint8_t);

typedef struct RadiusData {
    uint8_t code;
    uint8_t identifier;
    uint16_t length;
    span authentificator;
    option_Vector_radius_attribute attributes;
} radius_data;

void create_RadiusData (uint8_t code, uint8_t identifier, uint16_t length, span authentificator, option_Vector_radius_attribute attributes, radius_data* res){
    res->code = code;
    res->identifier = identifier;
    res->length = length;
    res->authentificator = authentificator;
    res->attributes = attributes;
}

void create_UserName(span s, radius_attribute* res) {
    res->key = 0;
    res->attribute.UserName.v = s;
}

void create_UserPassword(span s, radius_attribute* res) {
    res->key = 1;
    res->attribute.UserPassword.v = s;
}

void create_ChapPassword(uint8_t n, span s, radius_attribute* res) {
    res->key = 2;
    res->attribute.ChapPassword.n = n;
    res->attribute.ChapPassword.v = s;
}

void create_NasIPAddress(ipv4 ip, radius_attribute* res) {
    res->key = 3;
    res->attribute.NasIPAddress.ip = ip;
}

void create_NasPort(uint32_t v, radius_attribute* res) {
    res->key = 4;
    res->attribute.NasPort.v = v;
}

void create_Protocol(uint32_t v, radius_attribute* res) {
    res->key = 5;
    res->attribute.Protocol.v = v;
}

void create_FramedIPAddress(ipv4 ip, radius_attribute* res) {
    res->key = 6;
    res->attribute.FramedIPAddress.ip = ip;
}

void create_FramedIPNetmask(ipv4 ip, radius_attribute* res) {
    res->key = 7;
    res->attribute.FramedIPNetmask.ip = ip;
}


void create_Routing(uint32_t v, radius_attribute* res) {
    res->key = 8;
    res->attribute.Routing.v = v;
}

void create_FilterId(span s, radius_attribute* res) {
    res->key = 9;
    res->attribute.FilterId.s = s;
}

void create_FramedMTU(uint32_t v, radius_attribute* res) {
    res->key = 10;
    res->attribute.FramedMTU.v = v;
}

void create_Compression(uint32_t v, radius_attribute* res) {
    res->key = 11;
    res->attribute.Compression.v = v;
}

void create_VendorSpecific(uint32_t v, span s, radius_attribute* res) {
    res->key = 12;
    res->attribute.Compression.v = v;
    res->attribute.VendorSpecific.s = s;
}

void create_CalledStationId(span s, radius_attribute* res) {
    res->key = 13;
    res->attribute.CalledStationId.s = s;
}

void create_CallingStationId(span s, radius_attribute* res) {
    res->key = 14;
    res->attribute.CallingStationId.s = s;
}

void create_Unknown(uint8_t n, span s, radius_attribute* res) {
    res->key = 15;
    res->attribute.Unknown.n = n;
    res->attribute.Unknown.s = s;
}

void create_Service(uint32_t n, radius_attribute* res) {
    res->key = 16;
    res->attribute.Service.v = n;
}


void print_radius_attribute(radius_attribute attr) {
    switch (attr.key){
    case 0 :
        printf ("UserName :\n span :");
        print_span(attr.attribute.UserName.v);
        break;
    case 1 :
        printf ("UserPassword :\n span :");
        print_span(attr.attribute.UserPassword.v);
        break;
    case 2 :
        printf ("ChapPassword :\n n : %d\nspan :",attr.attribute.ChapPassword.n);
        print_span(attr.attribute.ChapPassword.v);
        break;
    case 3 :
        printf ("ChapPassword :\n ipv4 :");
        print_ipv4(attr.attribute.NasIPAddress.ip);
        break;
    case 4 :
        printf ("NasPort :\n uint32 :%d\n",attr.attribute.NasPort.v);
        break;
    case 5 :
        printf ("Protocol :\n uint32 :%d\n",attr.attribute.Protocol.v);
        break;
    case 6 :
        printf ("FramedIPAddress :\n ip :");
        print_ipv4(attr.attribute.FramedIPAddress.ip);
        break;
    case 7 :
        printf ("FramedIPNetmask :\n ip :");
        print_ipv4(attr.attribute.FramedIPNetmask.ip);
        break;
    case 8 :
        printf ("Routing :\n uint32 :%d\n",attr.attribute.Routing.v);
        break;
    case 9 :
        printf ("FilterId :\n span :");
        print_span(attr.attribute.FilterId.s);
        break;
    case 10 :
        printf ("FramedMTU :\n uint32 :%d\n",attr.attribute.FramedMTU.v);
        break;
    case 11 :
        printf ("Compression :\n uint32 :%d\n",attr.attribute.Compression.v);
        break;
    case 12 :
        printf ("VendorSpecific :\n uint32 :%d\nspan :",attr.attribute.VendorSpecific.v);
        print_span(attr.attribute.VendorSpecific.s);
        break;
    case 13 :
        printf ("CalledStationId :\n span :");
        print_span(attr.attribute.CalledStationId.s);
        break;
    case 14 :
        printf ("CallingStationId :\n span :");
        print_span(attr.attribute.CallingStationId.s);
        break;
    case 15 :
        printf ("Unknown :\n uint32 :%d\nspan :",attr.attribute.Unknown.n);
        print_span(attr.attribute.Unknown.s);
        break;
    case 16 :
        printf ("Compression :\n uint32 :%d\n",attr.attribute.Service.v);
        break;
    default :
        printf ("Résultat normalement impossible\n");
    }
}
