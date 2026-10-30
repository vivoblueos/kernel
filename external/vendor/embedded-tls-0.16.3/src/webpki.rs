use crate::config::{Certificate, TlsCipherSuite, TlsClock, TlsVerifier};
use crate::extensions::extension_data::signature_algorithms::SignatureScheme;
use crate::handshake::{
    certificate::{
        Certificate as OwnedCertificate, CertificateEntryRef, CertificateRef as ServerCertificate,
    },
    certificate_verify::CertificateVerify,
};
use crate::TlsError;
use core::marker::PhantomData;
use digest::Digest;
use heapless::Vec;
use webpki::DnsNameRef;

#[cfg(all(not(feature = "alloc"), feature = "webpki"))]
impl TryInto<&'static webpki::SignatureAlgorithm> for SignatureScheme {
    type Error = TlsError;
    fn try_into(self) -> Result<&'static webpki::SignatureAlgorithm, Self::Error> {
        // TODO: support other schemes via 'alloc' feature
        match self {
            SignatureScheme::RsaPkcs1Sha256 => Err(TlsError::InvalidSignatureScheme),
            SignatureScheme::RsaPkcs1Sha384 => Err(TlsError::InvalidSignatureScheme),
            SignatureScheme::RsaPkcs1Sha512 => Err(TlsError::InvalidSignatureScheme),

            /* ECDSA algorithms */
            SignatureScheme::EcdsaSecp256r1Sha256 => Ok(&webpki::ECDSA_P256_SHA256),
            SignatureScheme::EcdsaSecp384r1Sha384 => Ok(&webpki::ECDSA_P384_SHA384),
            SignatureScheme::EcdsaSecp521r1Sha512 => Err(TlsError::InvalidSignatureScheme),

            /* RSASSA-PSS algorithms with public key OID rsaEncryption */
            SignatureScheme::RsaPssRsaeSha256 => Err(TlsError::InvalidSignatureScheme),
            SignatureScheme::RsaPssRsaeSha384 => Err(TlsError::InvalidSignatureScheme),
            SignatureScheme::RsaPssRsaeSha512 => Err(TlsError::InvalidSignatureScheme),

            /* EdDSA algorithms */
            SignatureScheme::Ed25519 => Ok(&webpki::ED25519),
            SignatureScheme::Ed448 => Err(TlsError::InvalidSignatureScheme),

            /* RSASSA-PSS algorithms with public key OID RSASSA-PSS */
            SignatureScheme::RsaPssPssSha256 => Err(TlsError::InvalidSignatureScheme),
            SignatureScheme::RsaPssPssSha384 => Err(TlsError::InvalidSignatureScheme),
            SignatureScheme::RsaPssPssSha512 => Err(TlsError::InvalidSignatureScheme),

            /* Legacy algorithms */
            SignatureScheme::RsaPkcs1Sha1 => Err(TlsError::InvalidSignatureScheme),
            SignatureScheme::EcdsaSha1 => Err(TlsError::InvalidSignatureScheme),
        }
    }
}

#[cfg(all(feature = "alloc", feature = "webpki"))]
impl TryInto<&'static webpki::SignatureAlgorithm> for SignatureScheme {
    type Error = TlsError;
    fn try_into(self) -> Result<&'static webpki::SignatureAlgorithm, Self::Error> {
        match self {
            SignatureScheme::RsaPkcs1Sha256 => Ok(&webpki::RSA_PKCS1_2048_8192_SHA256),
            SignatureScheme::RsaPkcs1Sha384 => Ok(&webpki::RSA_PKCS1_2048_8192_SHA384),
            SignatureScheme::RsaPkcs1Sha512 => Ok(&webpki::RSA_PKCS1_2048_8192_SHA512),

            /* ECDSA algorithms */
            SignatureScheme::EcdsaSecp256r1Sha256 => Ok(&webpki::ECDSA_P256_SHA256),
            SignatureScheme::EcdsaSecp384r1Sha384 => Ok(&webpki::ECDSA_P384_SHA384),
            SignatureScheme::EcdsaSecp521r1Sha512 => Err(TlsError::InvalidSignatureScheme),

            /* RSASSA-PSS algorithms with public key OID rsaEncryption */
            SignatureScheme::RsaPssRsaeSha256 => Ok(&webpki::RSA_PSS_2048_8192_SHA256_LEGACY_KEY),
            SignatureScheme::RsaPssRsaeSha384 => Ok(&webpki::RSA_PSS_2048_8192_SHA384_LEGACY_KEY),
            SignatureScheme::RsaPssRsaeSha512 => Ok(&webpki::RSA_PSS_2048_8192_SHA512_LEGACY_KEY),

            /* EdDSA algorithms */
            SignatureScheme::Ed25519 => Ok(&webpki::ED25519),
            SignatureScheme::Ed448 => Err(TlsError::InvalidSignatureScheme),

            /* RSASSA-PSS algorithms with public key OID RSASSA-PSS */
            SignatureScheme::RsaPssPssSha256 => Err(TlsError::InvalidSignatureScheme),
            SignatureScheme::RsaPssPssSha384 => Err(TlsError::InvalidSignatureScheme),
            SignatureScheme::RsaPssPssSha512 => Err(TlsError::InvalidSignatureScheme),

            /* Legacy algorithms */
            SignatureScheme::RsaPkcs1Sha1 => Err(TlsError::InvalidSignatureScheme),
            SignatureScheme::EcdsaSha1 => Err(TlsError::InvalidSignatureScheme),
        }
    }
}

static ALL_SIGALGS: &[&webpki::SignatureAlgorithm] = &[
    &webpki::ECDSA_P256_SHA256,
    &webpki::ECDSA_P256_SHA384,
    &webpki::ECDSA_P384_SHA256,
    &webpki::ECDSA_P384_SHA384,
    &webpki::ED25519,
];

pub struct CertVerifier<'a, CipherSuite, Clock, const CERT_SIZE: usize>
where
    Clock: TlsClock,
    CipherSuite: TlsCipherSuite,
{
    host: Option<&'a str>,
    certificate_transcript: Option<CipherSuite::Hash>,
    certificate: Option<OwnedCertificate<CERT_SIZE>>,
    _clock: PhantomData<Clock>,
}

impl<'a, CipherSuite, Clock, const CERT_SIZE: usize> TlsVerifier<'a, CipherSuite>
    for CertVerifier<'a, CipherSuite, Clock, CERT_SIZE>
where
    CipherSuite: TlsCipherSuite,
    Clock: TlsClock,
{
    fn new(host: Option<&'a str>) -> Self {
        Self {
            host,
            certificate_transcript: None,
            certificate: None,
            _clock: PhantomData,
        }
    }

    fn verify_certificate(
        &mut self,
        transcript: &CipherSuite::Hash,
        ca: &Option<Certificate>,
        cert: ServerCertificate,
    ) -> Result<(), TlsError> {
        verify_certificate(self.host.clone(), ca, &cert, Clock::now())?;
        self.certificate.replace(cert.try_into()?);
        self.certificate_transcript.replace(transcript.clone());
        Ok(())
    }

    fn verify_signature(&mut self, verify: CertificateVerify) -> Result<(), TlsError> {
        let handshake_hash = unwrap!(self.certificate_transcript.take());
        let ctx_str = b"TLS 1.3, server CertificateVerify\x00";
        let mut msg: Vec<u8, 130> = Vec::new();
        msg.resize(64, 0x20).map_err(|_| TlsError::EncodeError)?;
        msg.extend_from_slice(ctx_str)
            .map_err(|_| TlsError::EncodeError)?;
        msg.extend_from_slice(&handshake_hash.finalize())
            .map_err(|_| TlsError::EncodeError)?;

        let certificate = unwrap!(self.certificate.as_ref()).try_into()?;
        verify_signature(&msg[..], certificate, verify)?;
        Ok(())
    }
}

fn verify_signature(
    message: &[u8],
    certificate: ServerCertificate,
    verify: CertificateVerify,
) -> Result<(), TlsError> {
    let mut verified = false;
    if !certificate.entries.is_empty() {
        // TODO: Support intermediates...
        if let CertificateEntryRef::X509(certificate) = certificate.entries[0] {
            let cert = webpki::EndEntityCert::try_from(certificate).map_err(|e| {
                warn!("Error loading cert: {:?}", e);
                TlsError::DecodeError
            })?;

            trace!(
                "Verifying with signature scheme {:?}",
                verify.signature_scheme
            );
            info!("Signature: {:x?}", verify.signature);
            let pkisig = verify.signature_scheme.try_into()?;
            match cert.verify_signature(pkisig, message, verify.signature) {
                Ok(_) => {
                    verified = true;
                }
                Err(e) => {
                    info!("Error verifying signature: {:?}", e);
                }
            }
        }
    }
    if !verified {
        return Err(TlsError::InvalidSignature);
    }
    Ok(())
}

fn verify_certificate(
    verify_host: Option<&str>,
    ca: &Option<Certificate>,
    certificate: &ServerCertificate,
    now: Option<u64>,
) -> Result<(), TlsError> {
    let mut verified = false;
    let mut host_verified = false;
    if let Some(Certificate::X509(ca)) = ca {
        let trust = webpki::TrustAnchor::try_from_cert_der(ca).map_err(|e| {
            warn!("Error loading CA: {:?}", e);
            TlsError::DecodeError
        })?;
        let anchors = &[trust];
        let anchors = webpki::TLSServerTrustAnchors(anchors);

        trace!("We got {} certificate entries", certificate.entries.len());

        if !certificate.entries.is_empty() {
            // TODO: Support intermediates...
            if let CertificateEntryRef::X509(certificate) = certificate.entries[0] {
                let cert = webpki::EndEntityCert::try_from(certificate).map_err(|e| {
                    warn!("Error loading cert: {:?}", e);
                    TlsError::DecodeError
                })?;

                let time = if let Some(now) = now {
                    webpki::Time::from_seconds_since_unix_epoch(now)
                } else {
                    // If no clock is provided, use certificate notAfter as the timestamp, if available
                    if let Ok(validity) = cert.validity() {
                        validity.not_after
                    } else {
                        webpki::Time::from_seconds_since_unix_epoch(0)
                    }
                };
                info!("Certificate is loaded!");
                match cert.verify_is_valid_tls_server_cert(ALL_SIGALGS, &anchors, &[], time) {
                    Ok(_) => verified = true,
                    Err(e) => {
                        warn!("Error verifying certificate: {:?}", e);
                    }
                }

                if let Some(server_name) = verify_host {
                    match cert.verify_is_valid_for_dns_name(
                        DnsNameRef::try_from_ascii_str(server_name).unwrap(),
                    ) {
                        Ok(_) => host_verified = true,
                        Err(e) => {
                            warn!("Error verifying host: {:?}", e);
                        }
                    }
                }
            }
        }
    }

    if !verified {
        return Err(TlsError::InvalidCertificate);
    }

    if !host_verified && verify_host.is_some() {
        return Err(TlsError::InvalidCertificate);
    }
    Ok(())
}
