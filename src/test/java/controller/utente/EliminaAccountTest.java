package controller.utente;

import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.mockito.Mockito.*;

class EliminaAccountTest {
    private EliminaAccount servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private UtenteDAO utenteDAO;
    private Utente utente;

    @BeforeEach
    void setUp() {
        servletUnderTest = new EliminaAccount();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        utenteDAO = mock(UtenteDAO.class);
        utente = mock(Utente.class);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utente);
        when(utente.getEmail()).thenReturn("test@example.com");

        servletUnderTest.setUtenteDAO(utenteDAO);
    }

    @Test
    void testDoGet_DeletesAccountAndRedirects() throws IOException {
        servletUnderTest.doGet(request, response);

        verify(utenteDAO).deleteUtente("test@example.com");
        verify(session).invalidate();
        verify(response).sendRedirect("index.html");
    }
}
