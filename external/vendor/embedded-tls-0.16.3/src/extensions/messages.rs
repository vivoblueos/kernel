use crate::extensions::{
    extension_data::{
        key_share::{KeyShareClientHello, KeyShareServerHello},
        max_fragment_length::MaxFragmentLength,
        pre_shared_key::{PreSharedKeyClientHello, PreSharedKeyServerHello},
        psk_key_exchange_modes::PskKeyExchangeModes,
        server_name::{ServerNameList, ServerNameResponse},
        signature_algorithms::SignatureAlgorithms,
        signature_algorithms_cert::SignatureAlgorithmsCert,
        supported_groups::SupportedGroups,
        supported_versions::{SupportedVersionsClientHello, SupportedVersionsServerHello},
        unimplemented::Unimplemented,
    },
    extension_group_macro::extension_group,
};

// Source: https://www.rfc-editor.org/rfc/rfc8446#section-4.2 table, rows marked with CH
extension_group! {
    pub enum ClientHelloExtension<'a> {
        ServerName(ServerNameList<'a, 1>),
        SupportedVersions(SupportedVersionsClientHello<16>),
        SignatureAlgorithms(SignatureAlgorithms<16>),
        SupportedGroups(SupportedGroups<16>),
        KeyShare(KeyShareClientHello<'a, 1>),
        PreSharedKey(PreSharedKeyClientHello<'a, 4>),
        PskKeyExchangeModes(PskKeyExchangeModes<4>),
        SignatureAlgorithmsCert(SignatureAlgorithmsCert<16>),
        MaxFragmentLength(MaxFragmentLength),
        StatusRequest(Unimplemented<'a>),
        UseSrtp(Unimplemented<'a>),
        Heartbeat(Unimplemented<'a>),
        ApplicationLayerProtocolNegotiation(Unimplemented<'a>),
        SignedCertificateTimestamp(Unimplemented<'a>),
        ClientCertificateType(Unimplemented<'a>),
        ServerCertificateType(Unimplemented<'a>),
        Padding(Unimplemented<'a>),
        EarlyData(Unimplemented<'a>),
        Cookie(Unimplemented<'a>),
        CertificateAuthorities(Unimplemented<'a>),
        OidFilters(Unimplemented<'a>),
        PostHandshakeAuth(Unimplemented<'a>)
    }
}

// Source: https://www.rfc-editor.org/rfc/rfc8446#section-4.2 table, rows marked with SH
extension_group! {
    pub enum ServerHelloExtension<'a> {
        KeyShare(KeyShareServerHello<'a>),
        PreSharedKey(PreSharedKeyServerHello),
        Cookie(Unimplemented<'a>), // temporary so we don't trip up on HelloRetryRequests
        SupportedVersions(SupportedVersionsServerHello)
    }
}

// Source: https://www.rfc-editor.org/rfc/rfc8446#section-4.2 table, rows marked with EE
extension_group! {
    pub enum EncryptedExtensionsExtension<'a> {
        ServerName(ServerNameResponse),
        MaxFragmentLength(MaxFragmentLength),
        SupportedGroups(SupportedGroups<10>),
        UseSrtp(Unimplemented<'a>),
        Heartbeat(Unimplemented<'a>),
        ApplicationLayerProtocolNegotiation(Unimplemented<'a>),
        ClientCertificateType(Unimplemented<'a>),
        ServerCertificateType(Unimplemented<'a>),
        EarlyData(Unimplemented<'a>)
    }
}

// Source: https://www.rfc-editor.org/rfc/rfc8446#section-4.2 table, rows marked with CR
extension_group! {
    pub enum CertificateRequestExtension<'a> {
        StatusRequest(Unimplemented<'a>),
        SignatureAlgorithms(SignatureAlgorithms<4>),
        SignedCertificateTimestamp(Unimplemented<'a>),
        CertificateAuthorities(Unimplemented<'a>),
        OidFilters(Unimplemented<'a>),
        SignatureAlgorithmsCert(Unimplemented<'a>)
    }
}

// Source: https://www.rfc-editor.org/rfc/rfc8446#section-4.2 table, rows marked with CT
extension_group! {
    pub enum CertificateExtension<'a> {
        StatusRequest(Unimplemented<'a>),
        SignedCertificateTimestamp(Unimplemented<'a>)
    }
}

// Source: https://www.rfc-editor.org/rfc/rfc8446#section-4.2 table, rows marked with NST
extension_group! {
    pub enum NewSessionTicketExtension<'a> {
        EarlyData(Unimplemented<'a>)
    }
}

// Source: https://www.rfc-editor.org/rfc/rfc8446#section-4.2 table, rows marked with HRR
extension_group! {
    pub enum HelloRetryRequestExtension<'a> {
        KeyShare(Unimplemented<'a>),
        Cookie(Unimplemented<'a>),
        SupportedVersions(Unimplemented<'a>)
    }
}
