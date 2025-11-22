package controller.utente;

import model.tesseraService.Tessera;
import model.tesseraService.TesseraDAO;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

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

}
