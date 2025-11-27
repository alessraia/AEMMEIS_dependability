package controller.utente;

import model.tesseraService.Tessera;
import model.tesseraService.TesseraDAO;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import org.junit.jupiter.api.Test;
import org.mockito.ArgumentCaptor;
import org.mockito.MockedConstruction;

import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.time.LocalDate;
import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

public class ModificaTipoServletTest {

    @Test
    public void premiumToStandard_callsDeleteAndUpdates() throws Exception {
        HttpServletRequest req = mock(HttpServletRequest.class);
        HttpServletResponse resp = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);

        Utente utente = new Utente();
        utente.setEmail("u@example.com");
        utente.setTipo("premium");

        when(req.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utente);

        Tessera tessera = new Tessera();
        tessera.setNumero("T123");

        try (MockedConstruction<TesseraDAO> tessMock = mockConstruction(TesseraDAO.class,
                (mock, ctx) -> {
                    when(mock.doRetrieveByEmail("u@example.com")).thenReturn(tessera);
                })) {
            try (MockedConstruction<UtenteDAO> utMock = mockConstruction(UtenteDAO.class)) {
                ModificaTipoServlet servlet = new ModificaTipoServlet();
                servlet.doGet(req, resp);

                // utente should be downgraded
                assertEquals("Standard", utente.getTipo());

                TesseraDAO constructedTess = tessMock.constructed().get(0);
                verify(constructedTess).deleteTessera("T123");

                UtenteDAO constructedUt = utMock.constructed().get(0);
                verify(constructedUt).updateUtente(utente);

                verify(resp).sendRedirect("area-personale");
            }
        }
    }

    @Test
    public void standardToPremium_createsTesseraAndUpdates() throws Exception {
        HttpServletRequest req = mock(HttpServletRequest.class);
        HttpServletResponse resp = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);

        Utente utente = new Utente();
        utente.setEmail("v@example.com");
        utente.setTipo("standard");

        when(req.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utente);

        try (MockedConstruction<TesseraDAO> tessMock = mockConstruction(TesseraDAO.class,
                (mock, ctx) -> {
                    when(mock.doRetrivedAllByNumero()).thenReturn(Arrays.asList("T111", "T222"));
                })) {
            try (MockedConstruction<UtenteDAO> utMock = mockConstruction(UtenteDAO.class)) {
                ModificaTipoServlet servlet = new ModificaTipoServlet();
                servlet.doGet(req, resp);

                // utente should be upgraded
                assertEquals("Premium", utente.getTipo());

                TesseraDAO constructedTess = tessMock.constructed().get(0);
                verify(constructedTess).doSave(any(Tessera.class));

                UtenteDAO constructedUt = utMock.constructed().get(0);
                verify(constructedUt).updateUtente(utente);

                verify(resp).sendRedirect("area-personale");
            }
        }
    }

    @Test
    public void standardToPremium_verifyTesseraFieldsAreSet() throws Exception {
        HttpServletRequest req = mock(HttpServletRequest.class);
        HttpServletResponse resp = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);

        Utente utente = new Utente();
        utente.setEmail("test@example.com");
        utente.setTipo("standard");

        when(req.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utente);

        ArgumentCaptor<Tessera> tesseraCaptor = ArgumentCaptor.forClass(Tessera.class);

        try (MockedConstruction<TesseraDAO> tessMock = mockConstruction(TesseraDAO.class,
                (mock, ctx) -> {
                    when(mock.doRetrivedAllByNumero()).thenReturn(Arrays.asList("T000", "T111"));
                })) {
            try (MockedConstruction<UtenteDAO> utMock = mockConstruction(UtenteDAO.class)) {
                ModificaTipoServlet servlet = new ModificaTipoServlet();
                servlet.doGet(req, resp);

                TesseraDAO constructedTess = tessMock.constructed().get(0);
                verify(constructedTess).doSave(tesseraCaptor.capture());

                Tessera savedTessera = tesseraCaptor.getValue();
                
                // Verify all fields are properly set
                assertEquals("test@example.com", savedTessera.getEmail());
                assertNotNull(savedTessera.getNumero());
                assertTrue(savedTessera.getNumero().startsWith("T"));
                assertEquals(3, savedTessera.getNumero().length() - 1); // "T" + 3 digits
                assertNotNull(savedTessera.getDataCreazione());
                assertEquals(LocalDate.now(), savedTessera.getDataCreazione());
                assertNotNull(savedTessera.getDataScadenza());
                assertEquals(LocalDate.now().plusYears(2), savedTessera.getDataScadenza());
            }
        }
    }

    @Test
    public void standardToPremium_numeroGenerationAvoidsCollisions() throws Exception {
        HttpServletRequest req = mock(HttpServletRequest.class);
        HttpServletResponse resp = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);

        Utente utente = new Utente();
        utente.setEmail("collision@example.com");
        utente.setTipo("standard");

        when(req.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utente);

        ArgumentCaptor<Tessera> tesseraCaptor = ArgumentCaptor.forClass(Tessera.class);

        // Create a list with many existing numbers to test collision avoidance
        try (MockedConstruction<TesseraDAO> tessMock = mockConstruction(TesseraDAO.class,
                (mock, ctx) -> {
                    when(mock.doRetrivedAllByNumero()).thenReturn(
                        Arrays.asList("T000", "T001", "T002", "T111", "T222", "T333")
                    );
                })) {
            try (MockedConstruction<UtenteDAO> utMock = mockConstruction(UtenteDAO.class)) {
                ModificaTipoServlet servlet = new ModificaTipoServlet();
                servlet.doGet(req, resp);

                TesseraDAO constructedTess = tessMock.constructed().get(0);
                verify(constructedTess).doSave(tesseraCaptor.capture());

                Tessera savedTessera = tesseraCaptor.getValue();
                String numero = savedTessera.getNumero();
                
                // Verify the generated number is not in the existing list
                assertFalse(Arrays.asList("T000", "T001", "T002", "T111", "T222", "T333").contains(numero));
                assertTrue(numero.startsWith("T"));
                assertEquals(4, numero.length());
            }
        }
    }

}
